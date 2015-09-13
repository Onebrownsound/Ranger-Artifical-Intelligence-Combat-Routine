using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Markup;
using Buddy.Coroutines;
using log4net;
using Loki.Bot;
using Loki.Bot.Logic.Bots.OldGrindBot;
using Loki.Bot.Pathfinding;
using Loki.Game;
using Loki.Game.GameData;
using Loki.Game.Objects;
using Loki.Common;
using Utility = Loki.Bot.Logic.Bots.OldGrindBot.Utility;

namespace OldRoutine
{
	/// <summary> </summary>
	public class OldRoutine : IRoutine
	{
		private static readonly ILog Log = Logger.GetLoggerInstanceForType();

		// Auto-set, you do not have to change these.
		private int _raiseZombieSlot = -1;
		private int _raiseSpectreSlot = -1;
		private int _animateWeaponSlot = -1;
		private int _animateGuardianSlot = -1;
		private int _flameblastSlot = -1;
		private int _enduringCrySlot = -1;
		private int _moltenShellSlot = -1;
		private int _bloodRageSlot = -1;
		private int _rfSlot = -1;
		private int _arcticArmourSlot = -1;
		private int _tempestShieldSlot = -1;
		private int _heraldOfAshSlot = -1;
		private int _heraldOfIceSlot = -1;
		private int _heraldOfThunderSlot = -1;
		private readonly List<int> _curseSlots = new List<int>();
		private int _auraSlot = -1;
		private int _totemSlot = -1;
		private int _trapSlot = -1;
		private int _mineSlot = -1;
		private int _summonSkeletonsSlot = -1;
		private int _summonRagingSpiritSlot = -1;
		private int _coldSnapSlot = -1;
		private int _frenzySlot = -1;

		private int _currentLeashRange = -1;

		private readonly Stopwatch _trapStopwatch = Stopwatch.StartNew();
		private readonly Stopwatch _totemStopwatch = Stopwatch.StartNew();
		private readonly Stopwatch _mineStopwatch = Stopwatch.StartNew();
		private readonly Stopwatch _animateWeaponStopwatch = Stopwatch.StartNew();
		private readonly Stopwatch _animateGuardianStopwatch = Stopwatch.StartNew();
		private readonly Stopwatch _moltenShellStopwatch = Stopwatch.StartNew();
		private readonly List<int> _ignoreAnimatedItems = new List<int>();
		private readonly Stopwatch _vaalStopwatch = Stopwatch.StartNew();

		private int _summonSkeletonCount;
		private readonly Stopwatch _summonSkeletonsStopwatch = Stopwatch.StartNew();

		private int _summonRagingSpiritCount;
		private readonly Stopwatch _summonRagingSpiritStopwatch = Stopwatch.StartNew();

		private bool _castingFlameblast;
		private int _lastFlameblastCharges;
		private bool _needsUpdate;

		private readonly Targeting _combatTargeting = new Targeting();

		private Dictionary<string, Func<dynamic[], object>> _exposedSettings;

		// http://stackoverflow.com/a/824854
		private void RegisterExposedSettings()
		{
			if (_exposedSettings != null)
				return;

			_exposedSettings = new Dictionary<string, Func<dynamic[], object>>();

			// Not a part of settings, so do it manually
			_exposedSettings.Add("SetLeash", param =>
			{
				_currentLeashRange = (int)param[0];
				return null;
			});

			_exposedSettings.Add("GetLeash", param =>
			{
				return _currentLeashRange;
			});

			// Automatically handle all settings

			PropertyInfo[] properties = typeof (OldRoutineSettings).GetProperties(BindingFlags.Public | BindingFlags.Instance);
			foreach (PropertyInfo p in properties)
			{
				// Only work with ints
				if (p.PropertyType != typeof (int) && p.PropertyType != typeof (bool))
				{
					continue;
				}

				// If not writable then cannot null it; if not readable then cannot check it's value
				if (!p.CanWrite || !p.CanRead)
				{
					continue;
				}

				MethodInfo mget = p.GetGetMethod(false);
				MethodInfo mset = p.GetSetMethod(false);

				// Get and set methods have to be public
				if (mget == null)
				{
					continue;
				}
				if (mset == null)
				{
					continue;
				}

				Log.InfoFormat("Name: {0} ({1})", p.Name, p.PropertyType);

				_exposedSettings.Add("Set" + p.Name, param =>
				{
					p.SetValue(OldRoutineSettings.Instance, param[0]);
					return null;
				});

				_exposedSettings.Add("Get" + p.Name, param =>
				{
					return p.GetValue(OldRoutineSettings.Instance);
				});
			}
		}

		private bool BlacklistedSkill(int id)
		{
			return false;
		}

		private Targeting CombatTargeting
		{
			get
			{
				return _combatTargeting;
			}
		}

		// Do not implement a ctor and do stuff in it.

		#region Targeting

		private void CombatTargetingOnWeightCalculation(NetworkObject entity, ref float weight)
		{
			weight -= entity.Distance/2;

			var m = entity as Monster;
			if (m == null)
				return;

			// If the monster is the source of Allies Cannot Die, we really want to kill it fast.
			if (m.HasAura("monster_aura_cannot_die"))
				weight += 40;

			if (m.IsTargetingMe)
			{
				weight += 20;
			}

			if (m.Rarity == Rarity.Magic)
			{
				weight += 5;
			}
			else if (m.Rarity == Rarity.Rare)
			{
				weight += 10;
			}
			else if (m.Rarity == Rarity.Unique)
			{
				weight += 15;
			}

			// Minions that get in the way.
			switch (m.Name)
			{
				case "Summoned Skeleton":
					weight -= 15;
					break;

				case "Raised Zombie":
					weight -= 15;
					break;
			}

			if (m.Rarity == Rarity.Normal && m.Type.Contains("/Totems/"))
			{
				weight -= 15;
			}

			// Necros
			if (m.ExplicitAffixes.Any(a => a.InternalName.Contains("RaisesUndead")) ||
				m.ImplicitAffixes.Any(a => a.InternalName.Contains("RaisesUndead")))
			{
				weight += 30;
			}

			// Ignore these mostly, as they just respawn.
			if (m.Type.Contains("TaniwhaTail"))
			{
				weight -= 30;
			}
		}

		private readonly string[] _aurasToIgnore = new[]
		{
			"shrine_godmode", // Ignore any mob near Divine Shrine
			"bloodlines_invulnerable", // Ignore Phylacteral Link
			"god_mode", // Ignore Animated Guardian
			"bloodlines_necrovigil",
		};

		private bool CombatTargetingOnInclusionCalcuation(NetworkObject entity)
		{
			try
			{
				var m = entity as Monster;
				if (m == null)
					return false;

				if (AreaStateCache.Current.IsBlacklisted(m))
					return false;

				// Do not consider inactive/dead mobs.
				if (!m.IsActive)
					return false;

				// Ignore any mob that cannot die.
				if (m.CannotDie)
					return false;

				// Ignore mobs that are too far to care about.
				if (m.Distance > (_currentLeashRange != -1 ? OldRoutineSettings.Instance.CombatRange : 300))
					return false;

				// Ignore mobs with special aura/buffs
				if (m.HasAura(_aurasToIgnore))
					return false;

				// Ignore Voidspawn of Abaxoth: thanks ExVault!
				if (m.ExplicitAffixes.Any(a => a.DisplayName == "Voidspawn of Abaxoth"))
					return false;

				// Ignore these mobs when trying to transition in the dom fight.
				// Flag1 has been seen at 5 or 6 at times, so need to work out something more reliable.
				if (m.Name == "Miscreation")
				{
					var dom = LokiPoe.ObjectManager.GetObjectByName<Monster>("Dominus, High Templar");
					if (dom != null && !dom.IsDead &&
						(dom.Components.TransitionableComponent.Flag1 == 6 || dom.Components.TransitionableComponent.Flag1 == 5))
					{
						AreaStateCache.Current.Blacklist(m.Id, TimeSpan.FromHours(1), "Miscreation");
						return false;
					}
				}

				// Ignore Piety's portals.
				if (m.Name == "Chilling Portal" || m.Name == "Burning Portal")
				{
					AreaStateCache.Current.Blacklist(m.Id, TimeSpan.FromHours(1), "Piety portal");
					return false;
				}
			}
			catch (Exception ex)
			{
				Log.Error("[CombatOnInclusionCalcuation]", ex);
				return false;
			}
			return true;
		}

		#endregion

		#region Implementation of IBase

		/// <summary>Initializes this routine.</summary>
		public void Initialize()
		{
			Log.DebugFormat("[OldRoutine] Initialize");

			_combatTargeting.InclusionCalcuation += CombatTargetingOnInclusionCalcuation;
			_combatTargeting.WeightCalculation += CombatTargetingOnWeightCalculation;

			RegisterExposedSettings();
		}

		/// <summary> </summary>
		public void Deinitialize()
		{
		}

		#endregion

		#region Implementation of IAuthored

		/// <summary>The name of the routine.</summary>
		public string Name
		{
			get
			{
				return "OldRoutine";
			}
		}

		/// <summary>The description of the routine.</summary>
		public string Description
		{
			get
			{
				return "An example routine for Exilebuddy.";
			}
		}

		/// <summary>
		/// The author of this object.
		/// </summary>
		public string Author
		{
			get
			{
				return "Bossland GmbH";
			}
		}

		/// <summary>
		/// The version of this routone.
		/// </summary>
		public string Version
		{
			get
			{
				return "0.0.1.1";
			}
		}

		#endregion

		#region Implementation of IRunnable

		/// <summary> The routine start callback. Do any initialization here. </summary>
		public void Start()
		{
			Log.DebugFormat("[OldRoutine] Start");

			_needsUpdate = true;

			if (OldRoutineSettings.Instance.SingleTargetMeleeSlot == -1 &&
				OldRoutineSettings.Instance.SingleTargetRangedSlot == -1 &&
				OldRoutineSettings.Instance.AoeMeleeSlot == -1 &&
				OldRoutineSettings.Instance.AoeRangedSlot == -1)
			{
				Log.ErrorFormat(
					"[Start] Please configure the OldRoutine settings (Settings -> OldRoutine) before starting!");
				BotManager.Stop();
			}
		}
		 private int FrenzyCharges
        {
            get
            {
                Aura aura = LokiPoe.ObjectManager.Me.Auras.FirstOrDefault(a => a.InternalName == "frenzy_charge");
                if (aura != null)
                {
                    return aura.Charges;
                }
                return 0;
            }
        }
		private bool IsCastableHelper(Skill skill)
		{
			return skill != null && skill.IsCastable && !skill.IsTotem && !skill.IsTrap && !skill.IsMine;
		}

		private bool IsAuraName(string name)
		{
			// This makes sure auras on items don't get used, since they don't have skill gems, and won't have an Aura tag.
			if (!OldRoutineSettings.Instance.EnableAurasFromItems)
			{
				return false;
			}

			var auraNames = new string[]
			{
				"Anger", "Clarity", "Determination", "Discipline", "Grace", "Haste", "Hatred", "Purity of Elements",
				"Purity of Fire", "Purity of Ice", "Purity of Lightning", "Vitality", "Wrath"
			};

			return auraNames.Contains(name);
		}

		/// <summary> The routine tick callback. Do any update logic here. </summary>
		public void Tick()
		{
			if (!LokiPoe.IsInGame)
				return;

			if (_needsUpdate)
			{
				_frenzySlot = -1;
				_raiseZombieSlot = -1;
				_raiseSpectreSlot = -1;
				_animateWeaponSlot = -1;
				_animateGuardianSlot = -1;
				_flameblastSlot = -1;
				_enduringCrySlot = -1;
				_moltenShellSlot = -1;
				_arcticArmourSlot = -1;
				_tempestShieldSlot = -1;
				_heraldOfAshSlot = -1;
				_heraldOfIceSlot = -1;
				_heraldOfThunderSlot = -1;
				_auraSlot = -1;
				_totemSlot = -1;
				_trapSlot = -1;
				_coldSnapSlot = -1;
				_bloodRageSlot = -1;
				_rfSlot = -1;
				_summonSkeletonsSlot = -1;
				_summonRagingSpiritSlot = -1;
				_summonSkeletonCount = 0;
				_summonRagingSpiritCount = 0;
				_mineSlot = -1;
				_curseSlots.Clear();

				// Register curses.
				foreach (var skill in LokiPoe.InGameState.SkillBarPanel.Skills)
				{
					var tags = skill.SkillTags;
					var name = skill.Name;

					if (tags.Contains("curse"))
					{
						var slot = skill.Slot;
						if (slot != -1 && skill.IsCastable)
						{
							_curseSlots.Add(slot);
						}
					}

					if (_auraSlot == -1 && ((tags.Contains("aura") && !tags.Contains("vaal")) || IsAuraName(name)))
					{
						_auraSlot = skill.Slot;
					}

					if (skill.IsTotem && _totemSlot == -1)
					{
						_totemSlot = skill.Slot;
					}

					if (skill.IsTrap && _trapSlot == -1)
					{
						_trapSlot = skill.Slot;
					}

					if (skill.IsMine && _mineSlot == -1)
					{
						_mineSlot = skill.Slot;
					}
				}

				//addition of Frenzy code here.
				var frenzy = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Frenzy");
				if (IsCastableHelper(frenzy))
				{
					_frenzySlot = frenzy.Slot;
				}

				var cs = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Cold Snap");
				if (IsCastableHelper(cs))
				{
					_coldSnapSlot = cs.Slot;
				}

				var hoa = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Herald of Ash");
				if (IsCastableHelper(hoa))
				{
					_heraldOfAshSlot = hoa.Slot;
				}

				var hoi = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Herald of Ice");
				if (IsCastableHelper(hoi))
				{
					_heraldOfIceSlot = hoi.Slot;
				}

				var hot = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Herald of Thunder");
				if (IsCastableHelper(hot))
				{
					_heraldOfThunderSlot = hot.Slot;
				}

				var ss = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Summon Skeletons");
				if (IsCastableHelper(ss))
				{
					_summonSkeletonsSlot = ss.Slot;
				}

				var srs = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Summon Raging Spirit");
				if (IsCastableHelper(srs))
				{
					_summonRagingSpiritSlot = srs.Slot;
				}

				var rf = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Righteous Fire");
				if (IsCastableHelper(rf))
				{
					_rfSlot = rf.Slot;
				}

				var br = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Blood Rage");
				if (IsCastableHelper(br))
				{
					_bloodRageSlot = br.Slot;
				}

				var ts = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Tempest Shield");
				if (IsCastableHelper(ts))
				{
					_tempestShieldSlot = ts.Slot;
				}

				var aa = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Arctic Armour");
				if (IsCastableHelper(aa))
				{
					_arcticArmourSlot = aa.Slot;
				}

				var mc = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Molten Shell");
				if (IsCastableHelper(mc))
				{
					_moltenShellSlot = mc.Slot;
				}

				var ec = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Enduring Cry");
				if (IsCastableHelper(ec))
				{
					_enduringCrySlot = ec.Slot;
				}

				var rz = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Raise Zombie");
				if (IsCastableHelper(rz))
				{
					_raiseZombieSlot = rz.Slot;
				}

				var rs = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Raise Spectre");
				if (IsCastableHelper(rs))
				{
					_raiseSpectreSlot = rs.Slot;
				}

				var fb = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Flameblast");
				if (IsCastableHelper(fb))
				{
					_flameblastSlot = fb.Slot;
				}

				var ag = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Animate Guardian");
				if (IsCastableHelper(ag))
				{
					_animateGuardianSlot = ag.Slot;
				}

				var aw = LokiPoe.InGameState.SkillBarPanel.Skills.FirstOrDefault(s => s.Name == "Animate Weapon");
				if (IsCastableHelper(aw))
				{
					_animateWeaponSlot = aw.Slot;
				}

				_needsUpdate = false;
			}
		}

		/// <summary> The routine stop callback. Do any pre-dispose cleanup here. </summary>
		public void Stop()
		{
			Log.DebugFormat("[OldRoutine] Stop");
		}

		#endregion

		#region Implementation of IConfigurable

		/// <summary> The bot's settings control. This will be added to the Exilebuddy Settings tab.</summary>
		public UserControl Control
		{
			get
			{
				using (var fs = new FileStream(@"Routines\OldRoutine\SettingsGui.xaml", FileMode.Open))
				{
					var root = (UserControl) XamlReader.Load(fs);

					// Your settings binding here.

					if (
						!Wpf.SetupCheckBoxBinding(root, "LeaveFrameCheckBox", "LeaveFrame",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupCheckBoxBinding failed for 'LeaveFrameCheckBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupCheckBoxBinding(root, "EnableAurasFromItemsCheckBox", "EnableAurasFromItems",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupCheckBoxBinding failed for 'EnableAurasFromItemsCheckBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupCheckBoxBinding(root, "AlwaysAttackInPlaceCheckBox", "AlwaysAttackInPlace",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupCheckBoxBinding failed for 'AlwaysAttackInPlaceCheckBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupCheckBoxBinding(root, "DebugAurasCheckBox", "DebugAuras",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupCheckBoxBinding failed for 'DebugAurasCheckBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupCheckBoxBinding(root, "AutoCastVaalSkillsCheckBox", "AutoCastVaalSkills",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupCheckBoxBinding failed for 'AutoCastVaalSkillsCheckBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxItemsBinding(root, "SingleTargetMeleeSlotComboBox", "AllSkillSlots",
							BindingMode.OneWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxItemsBinding failed for 'SingleTargetMeleeSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxSelectedItemBinding(root, "SingleTargetMeleeSlotComboBox",
							"SingleTargetMeleeSlot", BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxSelectedItemBinding failed for 'SingleTargetMeleeSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxItemsBinding(root, "SingleTargetRangedSlotComboBox", "AllSkillSlots",
							BindingMode.OneWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxItemsBinding failed for 'SingleTargetRangedSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxSelectedItemBinding(root, "SingleTargetRangedSlotComboBox",
							"SingleTargetRangedSlot", BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxSelectedItemBinding failed for 'SingleTargetRangedSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxItemsBinding(root, "AoeMeleeSlotComboBox", "AllSkillSlots",
							BindingMode.OneWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxItemsBinding failed for 'AoeMeleeSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxSelectedItemBinding(root, "AoeMeleeSlotComboBox",
							"AoeMeleeSlot", BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxSelectedItemBinding failed for 'AoeMeleeSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxItemsBinding(root, "AoeRangedSlotComboBox", "AllSkillSlots",
							BindingMode.OneWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxItemsBinding failed for 'AoeRangedSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxSelectedItemBinding(root, "AoeRangedSlotComboBox",
							"AoeRangedSlot", BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxSelectedItemBinding failed for 'AoeRangedSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxItemsBinding(root, "FallbackSlotComboBox", "AllSkillSlots",
							BindingMode.OneWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxItemsBinding failed for 'FallbackSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupComboBoxSelectedItemBinding(root, "FallbackSlotComboBox",
							"FallbackSlot", BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupComboBoxSelectedItemBinding failed for 'FallbackSlotComboBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "CombatRangeTextBox", "CombatRange",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat("[SettingsControl] SetupTextBoxBinding failed for 'CombatRangeTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "MaxMeleeRangeTextBox", "MaxMeleeRange",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat("[SettingsControl] SetupTextBoxBinding failed for 'MaxMeleeRangeTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "MaxRangeRangeTextBox", "MaxRangeRange",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat("[SettingsControl] SetupTextBoxBinding failed for 'MaxRangeRangeTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "MaxFlameBlastChargesTextBox", "MaxFlameBlastCharges",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'MaxFlameBlastChargesTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "MoltenShellDelayMsTextBox", "MoltenShellDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat("[SettingsControl] SetupTextBoxBinding failed for 'MoltenShellDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "TotemDelayMsTextBox", "TotemDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'TotemDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "TrapDelayMsTextBox", "TrapDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'TrapDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupTextBoxBinding(root, "SummonRagingSpiritCountPerDelayTextBox",
							"SummonRagingSpiritCountPerDelay",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'SummonRagingSpiritCountPerDelayTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "SummonRagingSpiritDelayMsTextBox", "SummonRagingSpiritDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'SummonRagingSpiritDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (
						!Wpf.SetupTextBoxBinding(root, "SummonSkeletonCountPerDelayTextBox",
							"SummonSkeletonCountPerDelay",
							BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'SummonSkeletonCountPerDelayTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "SummonSkeletonDelayMsTextBox", "SummonSkeletonDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'SummonSkeletonDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					if (!Wpf.SetupTextBoxBinding(root, "MineDelayMsTextBox", "MineDelayMs",
						BindingMode.TwoWay, OldRoutineSettings.Instance))
					{
						Log.DebugFormat(
							"[SettingsControl] SetupTextBoxBinding failed for 'MineDelayMsTextBox'.");
						throw new Exception("The SettingsControl could not be created.");
					}

					// Your settings event handlers here.

					return root;
				}
			}
		}

		/// <summary>The settings object. This will be registered in the current configuration.</summary>
		public JsonSettings Settings
		{
			get
			{
				return OldRoutineSettings.Instance;
			}
		}

		#endregion

		#region Implementation of ILogic

		/// <summary>
		/// Coroutine logic to execute.
		/// </summary>
		/// <param name="type">The requested type of logic to execute.</param>
		/// <param name="param">Data sent to the object from the caller.</param>
		/// <returns>true if logic was executed to handle this type and false otherwise.</returns>
		public async Task<bool> Logic(string type, params dynamic[] param)
		{
			if (type == "core_area_changed_event")
			{
				var oldSeed = (uint) param[0];
				var newSeed = (uint) param[1];
				var oldArea = (DatWorldAreaWrapper) param[2];
				var newArea = (DatWorldAreaWrapper) param[3];

				_ignoreAnimatedItems.Clear();

				return true;
			}

			if (type == "core_player_died_event")
			{
				var totalDeathsForInstance = (int) param[0];

				return true;
			}

			if (type == "core_player_leveled_event")
			{
				Log.InfoFormat("[Logic] We are now level {0}!", (int) param[0]);
				return true;
			}

			if (type == "combat")
			{
				// Update targeting.
				CombatTargeting.Update();

				// We now signal always highlight needs to be disabled, but won't actually do it until we cast something.
				if (
					LokiPoe.ObjectManager.GetObjectsByType<Chest>()
						.Any(c => c.Distance < 70 && !c.IsOpened && c.IsStrongBox))
				{
					_needsToDisableAlwaysHighlight = true;
				}
				else
				{
					_needsToDisableAlwaysHighlight = false;
				}

				var myPos = LokiPoe.Me.Position;

				// If we have flameblast, we need to use special logic for it.
				if (_flameblastSlot != -1)
				{
					if (_castingFlameblast)
					{
						var c = LokiPoe.Me.FlameblastCharges;

						// Handle being cast interrupted.
						if (c < _lastFlameblastCharges)
						{
							_castingFlameblast = false;
							return true;
						}
						_lastFlameblastCharges = c;

						if (c >= OldRoutineSettings.Instance.MaxFlameBlastCharges)
						{
							// Stop using the skill, so it's cast.
							await Coroutines.FinishCurrentAction();

							_castingFlameblast = false;
						}
						else
						{
							await DisableAlwaysHiglight();

							// Keep using the skill to build up charges.
							var buaerr = LokiPoe.InGameState.SkillBarPanel.UseAt(_flameblastSlot, false,
								myPos);
							if (buaerr != LokiPoe.InGameState.UseError.None)
							{
								Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", buaerr, "Flameblast");
							}
						}

						return true;
					}
				}

				// Limit this logic once per second, because it can get expensive and slow things down if run too fast.
				if (_animateGuardianSlot != -1 && _animateGuardianStopwatch.ElapsedMilliseconds > 1000)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_animateGuardianSlot);
					if (skill.CanUse())
					{
						// Check for a target near us.
						var target = BestAnimateGuardianTarget(skill.DeployedObjects.FirstOrDefault() as Monster,
							skill.GetStat(StatTypeGGG.AnimateItemMaximumLevelRequirement));
						if (target != null)
						{
							await DisableAlwaysHiglight();

							Log.InfoFormat("[Logic] Using {0} on {1}.", skill.Name, target.Name);

							var uaerr = LokiPoe.InGameState.SkillBarPanel.UseOn(_animateGuardianSlot, true, target);
							if (uaerr == LokiPoe.InGameState.UseError.None)
							{
								await Coroutines.FinishCurrentAction(false);

								await Coroutine.Sleep(Utility.LatencySafeValue(100));

								// We need to remove the item highlighting.
								LokiPoe.ProcessHookManager.ClearAllKeyStates();

								return true;
							}

							Log.ErrorFormat("[Logic] UseOn returned {0} for {1}.", uaerr, skill.Name);
						}

						_animateGuardianStopwatch.Restart();
					}
				}

				// Limit this logic once per second, because it can get expensive and slow things down if run too fast.
				if (_animateWeaponSlot != -1 && _animateWeaponStopwatch.ElapsedMilliseconds > 1000)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_animateWeaponSlot);
					if (skill.CanUse())
					{
						// Check for a target near us.
						var target = BestAnimateWeaponTarget(skill.GetStat(StatTypeGGG.AnimateItemMaximumLevelRequirement));
						if (target != null)
						{
							await DisableAlwaysHiglight();

							Log.InfoFormat("[Logic] Using {0} on {1}.", skill.Name, target.Name);

							var uaerr = LokiPoe.InGameState.SkillBarPanel.UseOn(_animateWeaponSlot, true, target);
							if (uaerr == LokiPoe.InGameState.UseError.None)
							{
								await Coroutines.FinishCurrentAction(false);

								await Coroutine.Sleep(Utility.LatencySafeValue(100));

								// We need to remove the item highlighting.
								LokiPoe.ProcessHookManager.ClearAllKeyStates();

								_animateWeaponStopwatch.Restart();

								return true;
							}

							Log.ErrorFormat("[Logic] UseOn returned {0} for {1}.", uaerr, skill.Name);
						}

						_animateWeaponStopwatch.Restart();
					}
				}

				// If we have Raise Spectre, we can look for dead bodies to use for our army as we move around.
				if (_raiseSpectreSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_raiseSpectreSlot);
					if (skill.CanUse())
					{
						var max = skill.GetStat(StatTypeGGG.NumberOfSpectresAllowed);
						if (skill.NumberDeployed < max)
						{
							// Check for a target near us.
							var target = BestDeadTarget;
							if (target != null)
							{
								await DisableAlwaysHiglight();

								Log.InfoFormat("[Logic] Using {0} on {1}.", skill.Name, target.Name);

								var uaerr = LokiPoe.InGameState.SkillBarPanel.UseAt(_raiseSpectreSlot, false,
									target.Position);
								if (uaerr == LokiPoe.InGameState.UseError.None)
								{
									await Coroutines.FinishCurrentAction(false);

									await Coroutine.Sleep(Utility.LatencySafeValue(100));

									return true;
								}

								Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", uaerr, skill.Name);
							}
						}
					}
				}

				// If we have Raise Zombie, we can look for dead bodies to use for our army as we move around.
				if (_raiseZombieSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_raiseZombieSlot);
					if (skill.CanUse())
					{
						var max = skill.GetStat(StatTypeGGG.NumberOfZombiesAllowed);
						if (skill.NumberDeployed < max)
						{
							// Check for a target near us.
							var target = BestDeadTarget;
							if (target != null)
							{
								await DisableAlwaysHiglight();

								Log.InfoFormat("[Logic] Using {0} on {1}.", skill.Name, target.Name);

								var uaerr = LokiPoe.InGameState.SkillBarPanel.UseAt(_raiseZombieSlot, false,
									target.Position);
								if (uaerr == LokiPoe.InGameState.UseError.None)
								{
									await Coroutines.FinishCurrentAction(false);

									await Coroutine.Sleep(Utility.LatencySafeValue(100));

									return true;
								}

								Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", uaerr, skill.Name);
							}
						}
					}
				}

				// Simply cast Tempest Shield if we have it.
				if (_tempestShieldSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_tempestShieldSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasTempestShieldBuff)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_tempestShieldSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Simply cast Hearld of Ash if we have it.
				if (_heraldOfAshSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_heraldOfAshSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasHeraldOfAshBuff)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_heraldOfAshSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Simply cast Hearld of Ice if we have it.
				if (_heraldOfIceSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_heraldOfIceSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasHeraldOfIceBuff)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_heraldOfIceSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Simply cast Hearld of Thunder if we have it.
				if (_heraldOfThunderSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_heraldOfThunderSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasHeraldOfThunderBuff)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_heraldOfThunderSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Since EC has a cooldown, we can just cast it when mobs are in range to keep our endurance charges refreshed.
				if (_enduringCrySlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_enduringCrySlot);
					if (skill.CanUse())
					{
						if (Utility.NumberOfMobsNear(LokiPoe.Me, 30) > 0)
						{
							var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_enduringCrySlot, true);
							if (err1 == LokiPoe.InGameState.UseError.None)
							{
								await Coroutine.Sleep(Utility.LatencySafeValue(500));

								await Coroutines.FinishCurrentAction(false);

								return true;
							}

							Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
						}
					}
				}

				// For Molten Shell, we want to limit cast time, since mobs that break the shield often would cause the CR to cast it over and over.
				if (_moltenShellSlot != -1 &&
					_moltenShellStopwatch.ElapsedMilliseconds >= OldRoutineSettings.Instance.MoltenShellDelayMs)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_moltenShellSlot);
					if (!LokiPoe.Me.HasMoltenShellBuff && skill.CanUse())
					{
						if (Utility.NumberOfMobsNear(LokiPoe.Me, OldRoutineSettings.Instance.CombatRange) > 0)
						{
							var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_moltenShellSlot, true);

							_moltenShellStopwatch.Restart();

							if (err1 == LokiPoe.InGameState.UseError.None)
							{
								await Coroutine.Sleep(Utility.LatencySafeValue(500));

								await Coroutines.FinishCurrentAction(false);

								await Coroutine.Sleep(Utility.LatencySafeValue(100));

								return true;
							}

							Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
						}
					}
				}

				// Handle Arctic Armour conditionally.
				if (_arcticArmourSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_arcticArmourSlot);
					if (!LokiPoe.Me.HasArcticArmourBuff && skill.CanUse())
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_arcticArmourSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Handle aura logic.
				if (_auraSlot != -1)
				{
					var aura = LokiPoe.InGameState.SkillBarPanel.Slot(_auraSlot);
					if (!LokiPoe.Me.HasAura(aura.Name) && aura.CanUse(OldRoutineSettings.Instance.DebugAuras) &&
						!BlacklistedSkill(aura.Id))
					{
						await Coroutines.FinishCurrentAction();

						await Coroutine.Sleep(Utility.LatencySafeValue(1000));

						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_auraSlot, false);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(250));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(1000));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, aura.Name);
					}

					foreach (var skill in LokiPoe.InGameState.SkillBarPanel.Skills)
					{
						if (BlacklistedSkill(skill.Id))
							continue;

						if ((skill.SkillTags.Contains("aura") && !skill.SkillTags.Contains("vaal")) || IsAuraName(skill.Name))
						{
							if (!LokiPoe.Me.HasAura(skill.Name) && skill.CanUse(OldRoutineSettings.Instance.DebugAuras, true))
							{
								var doCast = true;

								while (skill.Slot == -1)
								{
									Log.InfoFormat("[Logic] Now assigning {0} to the skillbar.", skill.Name);

									var sserr = LokiPoe.InGameState.SkillBarPanel.SetSlot(_auraSlot, skill);

									if (sserr != LokiPoe.InGameState.SetSlotError.None)
									{
										Log.ErrorFormat("[Logic] SetSlot returned {0}.", sserr);

										doCast = false;

										break;
									}

									await Coroutine.Sleep(Utility.LatencySafeValue(1000));
								}

								if (!doCast)
								{
									continue;
								}

								await Coroutines.FinishCurrentAction();

								await Coroutine.Sleep(Utility.LatencySafeValue(1000));

								var err1 = LokiPoe.InGameState.SkillBarPanel.Use(skill.Slot, false);
								if (err1 == LokiPoe.InGameState.UseError.None)
								{
									await Coroutine.Sleep(Utility.LatencySafeValue(250));

									await Coroutines.FinishCurrentAction(false);

									await Coroutine.Sleep(Utility.LatencySafeValue(1000));

									return true;
								}

								Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
							}
						}
					}
				}

				// Check for a surround to use flameblast, just example logic.
				if (_flameblastSlot != -1)
				{
					if (Utility.NumberOfMobsNear(LokiPoe.Me, 15) >= 4)
					{
						_castingFlameblast = true;
						_lastFlameblastCharges = 0;
						return true;
					}
				}

				// TODO: _currentLeashRange of -1 means we need to use a cached location system to prevent back and forth issues of mobs despawning.

				// This is pretty important. Otherwise, components can go invalid and exceptions are thrown.
				var bestTarget = CombatTargeting.Targets<Monster>().FirstOrDefault();

				// No monsters, we can execute non-critical combat logic, like buffs, auras, etc...
				// For this example, just going to continue executing bot logic.
				if (bestTarget == null)
				{
					if (await HandleShrines())
					{
						return true;
					}

					return await CombatLogicEnd();
				}

				var cachedPosition = bestTarget.Position;
				var targetPosition = bestTarget.ModelCenterWorld;
				var cachedId = bestTarget.Id;
				var cachedName = bestTarget.Name;
				var cachedRarity = bestTarget.Rarity;
				var cachedDistance = bestTarget.Distance;
				var cachedIsCursable = bestTarget.IsCursable;
				var cachedCurseCount = bestTarget.CurseCount;
				var cachedHasCurseFrom = new Dictionary<string, bool>();
				var cachedNumberOfMobsNear = Utility.NumberOfMobsNear(bestTarget, 20);
				var cachedProxShield = bestTarget.HasProximityShield;
				var cachedMobsNearForAoe = Utility.NumberOfMobsNear(LokiPoe.Me,
					OldRoutineSettings.Instance.MaxMeleeRange);
				var cachedMobsNearForCurse = Utility.NumberOfMobsNear(bestTarget, 20);

				foreach (var curseSlot in _curseSlots)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(curseSlot);
					cachedHasCurseFrom.Add(skill.Name, bestTarget.HasCurseFrom(skill.Name));
				}

				if (await HandleShrines())
				{
					return true;
				}

				var canSee = ExilePather.CanObjectSee(LokiPoe.Me, bestTarget, !OldRoutineSettings.Instance.LeaveFrame);
				var pathDistance = ExilePather.PathDistance(myPos, cachedPosition, true, !OldRoutineSettings.Instance.LeaveFrame);
				var blockedByDoor = Utility.ClosedDoorBetween(LokiPoe.Me, bestTarget, 10, 10,
					!OldRoutineSettings.Instance.LeaveFrame);

				if (pathDistance.CompareTo(float.MaxValue) == 0)
				{
					Log.ErrorFormat(
						"[Logic] Could not determine the path distance to the best target. Now blacklisting it.");
					AreaStateCache.Current.Blacklist(cachedId, TimeSpan.FromMinutes(1), "Unable to pathfind to.");
					return true;
				}

				// Prevent combat loops from happening by preventing combat outside CombatRange.
				if (pathDistance > OldRoutineSettings.Instance.CombatRange)
				{
					await EnableAlwaysHiglight();

					return false;
				}

				if (!canSee || blockedByDoor)
				{
					Log.InfoFormat(
						"[Logic] Now moving towards the monster {0} because [canSee: {1}][pathDistance: {2}][blockedByDoor: {3}]",
						cachedName, canSee, pathDistance, blockedByDoor);

					if (!PlayerMover.MoveTowards(cachedPosition))
					{
						Log.ErrorFormat("[Logic] MoveTowards failed for {0}.", cachedPosition);
					}

					return true;
				}

				// Handle totem logic.
				if (_totemSlot != -1 &&
					_totemStopwatch.ElapsedMilliseconds > OldRoutineSettings.Instance.TotemDelayMs)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_totemSlot);
					if (skill.CanUse() &&
						skill.DeployedObjects.Select(o => o as Monster).Count(t => !t.IsDead && t.Distance < 60) <
						LokiPoe.Me.MaxTotemCount)
					{
						await DisableAlwaysHiglight();

						var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_totemSlot, true,
							myPos.GetPointAtDistanceAfterThis(cachedPosition,
								cachedDistance/2));

						_totemStopwatch.Restart();

						if (err1 == LokiPoe.InGameState.UseError.None)
							return true;

						Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Handle trap logic.
				if (_trapSlot != -1 &&
					_trapStopwatch.ElapsedMilliseconds > OldRoutineSettings.Instance.TrapDelayMs)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_trapSlot);
					if (skill.CanUse())
					{
						await DisableAlwaysHiglight();

						var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_trapSlot, true,
							myPos.GetPointAtDistanceAfterThis(cachedPosition,
								cachedDistance/2));

						_trapStopwatch.Restart();

						if (err1 == LokiPoe.InGameState.UseError.None)
							return true;

						Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Handle curse logic - curse magic+ and packs of 4+, but only cast within MaxRangeRange.
				var checkCurses = myPos.Distance(cachedPosition) < OldRoutineSettings.Instance.MaxRangeRange &&
								(cachedRarity >= Rarity.Magic || cachedMobsNearForCurse >= 3);
				if (checkCurses)
				{
					foreach (var curseSlot in _curseSlots)
					{
						var skill = LokiPoe.InGameState.SkillBarPanel.Slot(curseSlot);
						if (skill.CanUse() &&
							cachedIsCursable &&
							cachedCurseCount < LokiPoe.Me.TotalCursesAllowed &&
							!cachedHasCurseFrom[skill.Name])
						{
							await DisableAlwaysHiglight();

							var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(curseSlot, true, cachedPosition);
							if (err1 == LokiPoe.InGameState.UseError.None)
								return true;

							Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
						}
					}
				}
				

				// Simply cast Blood Rage if we have it.
				if (_bloodRageSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_bloodRageSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasBloodRageBuff && cachedDistance < OldRoutineSettings.Instance.CombatRange)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_bloodRageSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}
				 

				// Simply cast RF if we have it.
				if (_rfSlot != -1)
				{
					// See if we can use the skill.
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_rfSlot);
					if (skill.CanUse() && !LokiPoe.Me.HasRighteousFireBuff)
					{
						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_rfSlot, true);
						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							await Coroutine.Sleep(Utility.LatencySafeValue(100));

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Frenzy for charges and cursed
                if (_frenzySlot != -1)
                {
                    // See if we can use the skill.
                    var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_frenzySlot);
                    if (skill.CanUse())
                    {
                        if (FrenzyCharges < (LokiPoe.ObjectManager.Me.GetStat(StatTypeGGG.MaxFrenzyCharges)-2) )
                        {
                            if (Utility.NumberOfMobsNear(LokiPoe.Me, 60) > 0)
                            {
                                Log.ErrorFormat(" Blah Blah something about frenzy");
                                
                               
                                var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_frenzySlot, false,targetPosition);

                                if (err1 == LokiPoe.InGameState.UseError.None)
                                {
                                    await Coroutine.Sleep(Utility.LatencySafeValue(500));

                                    await Coroutines.FinishCurrentAction(false);

                                    return true;
                                }

                                Log.ErrorFormat("[Logic] Used Frenzy");
                            }
                        }
                    }
                }
				if (_summonRagingSpiritSlot != -1 &&
					_summonRagingSpiritStopwatch.ElapsedMilliseconds >
					OldRoutineSettings.Instance.SummonRagingSpiritDelayMs)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_summonRagingSpiritSlot);
					var max = skill.GetStat(StatTypeGGG.NumberOfRagingSpiritsAllowed);
					if (skill.NumberDeployed < max && skill.CanUse())
					{
						++_summonRagingSpiritCount;

						var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_summonRagingSpiritSlot, false, targetPosition);

						if (_summonRagingSpiritCount >=
							OldRoutineSettings.Instance.SummonRagingSpiritCountPerDelay)
						{
							_summonRagingSpiritCount = 0;
							_summonRagingSpiritStopwatch.Restart();
						}

						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							return true;
						}

						Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
					}
				}

				if (_summonSkeletonsSlot != -1 &&
					_summonSkeletonsStopwatch.ElapsedMilliseconds >
					OldRoutineSettings.Instance.SummonSkeletonDelayMs)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_summonSkeletonsSlot);
					var max = skill.GetStat(StatTypeGGG.NumberOfSkeletonsAllowed);
					if (skill.NumberDeployed < max && skill.CanUse())
					{
						++_summonSkeletonCount;

						await DisableAlwaysHiglight();

						var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_summonSkeletonsSlot, true,
							myPos.GetPointAtDistanceAfterThis(cachedPosition,
								cachedDistance/2));

						if (_summonSkeletonCount >= OldRoutineSettings.Instance.SummonSkeletonCountPerDelay)
						{
							_summonSkeletonCount = 0;
							_summonSkeletonsStopwatch.Restart();
						}

						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutines.FinishCurrentAction(false);

							return true;
						}

						Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", err1, skill.Name);
					}
				}

				if (_mineSlot != -1 && _mineStopwatch.ElapsedMilliseconds >
					OldRoutineSettings.Instance.MineDelayMs &&
					myPos.Distance(cachedPosition) < OldRoutineSettings.Instance.MaxMeleeRange)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_mineSlot);
					var max = skill.GetStat(StatTypeGGG.SkillDisplayNumberOfRemoteMinesAllowed);
					var insta = skill.GetStat(StatTypeGGG.MineDetonationIsInstant) == 1;
					if (skill.NumberDeployed < max && skill.CanUse())
					{
						await DisableAlwaysHiglight();

						var err1 = LokiPoe.InGameState.SkillBarPanel.Use(_mineSlot, true);

						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(500));

							await Coroutines.FinishCurrentAction(false);

							if (!insta)
							{
								await Coroutine.Sleep(Utility.LatencySafeValue(350));

								LokiPoe.Input.PressKey(LokiPoe.Input.Binding.detonate_mines);
							}

							_mineStopwatch.Restart();

							return true;
						}

						_mineStopwatch.Restart();

						Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Handle cold snap logic. Only use when power charges won't be consumed.
				if (_coldSnapSlot != -1)
				{
					var skill = LokiPoe.InGameState.SkillBarPanel.Slot(_coldSnapSlot);
					if (skill.CanUse(false, false, false))
					{
						await DisableAlwaysHiglight();

						var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(_coldSnapSlot, true, cachedPosition);

						if (err1 == LokiPoe.InGameState.UseError.None)
						{
							await Coroutine.Sleep(Utility.LatencySafeValue(250));

							await Coroutines.FinishCurrentAction(false);

							return true;
						}

						Log.ErrorFormat("[Logic] UseAt returned {0} for {1}.", err1, skill.Name);
					}
				}

				// Auto-cast any vaal skill at the best target as soon as it's usable.
				if (OldRoutineSettings.Instance.AutoCastVaalSkills && _vaalStopwatch.ElapsedMilliseconds > 1000)
				{
					foreach (var skill in LokiPoe.InGameState.SkillBarPanel.Skills)
					{
						if (skill.SkillTags.Contains("vaal"))
						{
							if (skill.CanUse())
							{
								await DisableAlwaysHiglight();

								var err1 = LokiPoe.InGameState.SkillBarPanel.UseAt(skill.Slot, false, cachedPosition);
								if (err1 == LokiPoe.InGameState.UseError.None)
								{
									await Coroutine.Sleep(Utility.LatencySafeValue(250));

									await Coroutines.FinishCurrentAction(false);

									await Coroutine.Sleep(Utility.LatencySafeValue(1000));

									return true;
								}

								Log.ErrorFormat("[Logic] Use returned {0} for {1}.", err1, skill.Name);
							}
						}
					}
					_vaalStopwatch.Restart();
				}

				var aip = false;

				var aoe = false;
				var melee = false;

				int slot;

				// Logic for figuring out if we should use an AoE skill or single target.
				if (cachedNumberOfMobsNear > 2 && cachedRarity < Rarity.Rare)
				{
					aoe = true;
				}

				// Logic for figuring out if we should use an AoE skill instead.
				if (myPos.Distance(cachedPosition) < OldRoutineSettings.Instance.MaxMeleeRange)
				{
					melee = true;
					if (cachedMobsNearForAoe >= 3)
					{
						aoe = true;
					}
					else
					{
						aoe = false;
					}
				}

				// This sillyness is for making sure we always use a skill, and is why generic code is a PITA
				// when it can be configured like so.
				if (aoe)
				{
					if (melee)
					{
						slot = EnsurceCast(OldRoutineSettings.Instance.AoeMeleeSlot);
						if (slot == -1)
						{
							slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetMeleeSlot);
							if (slot == -1)
							{
								melee = false;
								slot = EnsurceCast(OldRoutineSettings.Instance.AoeRangedSlot);
								if (slot == -1)
								{
									slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetRangedSlot);
								}
							}
						}
					}
					else
					{
						slot = EnsurceCast(OldRoutineSettings.Instance.AoeRangedSlot);
						if (slot == -1)
						{
							slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetRangedSlot);
							if (slot == -1)
							{
								melee = true;
								slot = EnsurceCast(OldRoutineSettings.Instance.AoeMeleeSlot);
								if (slot == -1)
								{
									slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetMeleeSlot);
								}
							}
						}
					}
				}
				else
				{
					if (melee)
					{
						slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetMeleeSlot);
						if (slot == -1)
						{
							slot = EnsurceCast(OldRoutineSettings.Instance.AoeMeleeSlot);
							if (slot == -1)
							{
								melee = false;
								slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetRangedSlot);
								if (slot == -1)
								{
									slot = EnsurceCast(OldRoutineSettings.Instance.AoeRangedSlot);
								}
							}
						}
					}
					else
					{
						slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetRangedSlot);
						if (slot == -1)
						{
							slot = EnsurceCast(OldRoutineSettings.Instance.AoeRangedSlot);
							if (slot == -1)
							{
								melee = true;
								slot = EnsurceCast(OldRoutineSettings.Instance.SingleTargetMeleeSlot);
								if (slot == -1)
								{
									slot = EnsurceCast(OldRoutineSettings.Instance.AoeMeleeSlot);
								}
							}
						}
					}
				}

				if (OldRoutineSettings.Instance.AlwaysAttackInPlace)
					aip = true;

				if (slot == -1)
				{
					slot = OldRoutineSettings.Instance.FallbackSlot;
					melee = true;
				}

				if (melee || cachedProxShield)
				{
					var dist = LokiPoe.Me.Position.Distance(cachedPosition);
					if (dist > OldRoutineSettings.Instance.MaxMeleeRange)
					{
						Log.InfoFormat("[Logic] Now moving towards {0} because [dist ({1}) > MaxMeleeRange ({2})]",
							cachedPosition, dist, OldRoutineSettings.Instance.MaxMeleeRange);

						if (!PlayerMover.MoveTowards(cachedPosition))
						{
							Log.ErrorFormat("[Logic] MoveTowards failed for {0}.", cachedPosition);
						}
						return true;
					}
				}
				else
				{
					var dist = LokiPoe.Me.Position.Distance(cachedPosition);
					if (dist > OldRoutineSettings.Instance.MaxRangeRange)
					{
						Log.InfoFormat("[Logic] Now moving towards {0} because [dist ({1}) > MaxRangeRange ({2})]",
							cachedPosition, dist, OldRoutineSettings.Instance.MaxRangeRange);

						if (!PlayerMover.MoveTowards(cachedPosition))
						{
							Log.ErrorFormat("[Logic] MoveTowards failed for {0}.", cachedPosition);
						}
						return true;
					}
				}

				await DisableAlwaysHiglight();

				var err = LokiPoe.InGameState.SkillBarPanel.UseAt(slot, aip, targetPosition);
				if (err != LokiPoe.InGameState.UseError.None)
				{
					Log.ErrorFormat("[Logic] UseAt returned {0}.", err);
				}

				return true;
			}

			return false;
		}

		/// <summary>
		/// Non-coroutine logic to execute.
		/// </summary>
		/// <param name="name">The name of the logic to invoke.</param>
		/// <param name="param">The data passed to the logic.</param>
		/// <returns>Data from the executed logic.</returns>
		public object Execute(string name, params dynamic[] param)
		{
			Func<dynamic[], object> f;
			if (_exposedSettings.TryGetValue(name, out f))
			{
				return f(param);
			}

			return null;
		}

		#endregion

		private WorldItem BestAnimateGuardianTarget(Monster monster, int maxLevel)
		{
			var worldItems = LokiPoe.ObjectManager.GetObjectsByType<WorldItem>()
				.Where(wi => !_ignoreAnimatedItems.Contains(wi.Id) && wi.Distance < 30)
				.OrderBy(wi => wi.Distance);
			foreach (var wi in worldItems)
			{
				var item = wi.Item;
				if (item.RequiredLevel <= maxLevel &&
					item.IsIdentified &&
					!item.IsChromatic &&
					item.SocketCount < 5 &&
					item.MaxLinkCount < 5 &&
					item.Rarity <= Rarity.Magic
					)
				{
					if (monster == null || monster.LeftHandWeaponVisual == "")
					{
						if (item.IsClawType || item.IsOneHandAxeType || item.IsOneHandMaceType ||
							item.IsOneHandSwordType ||
							item.IsOneHandThrustingSwordType || item.IsTwoHandAxeType || item.IsTwoHandMaceType ||
							item.IsTwoHandSwordType)
						{
							_ignoreAnimatedItems.Add(wi.Id);
							return wi;
						}
					}

					if (monster == null || monster.ChestVisual == "")
					{
						if (item.IsBodyArmorType)
						{
							_ignoreAnimatedItems.Add(wi.Id);
							return wi;
						}
					}

					if (monster == null || monster.HelmVisual == "")
					{
						if (item.IsHelmetType)
						{
							_ignoreAnimatedItems.Add(wi.Id);
							return wi;
						}
					}

					if (monster == null || monster.BootsVisual == "")
					{
						if (item.IsBootType)
						{
							_ignoreAnimatedItems.Add(wi.Id);
							return wi;
						}
					}

					if (monster == null || monster.GlovesVisual == "")
					{
						if (item.IsGloveType)
						{
							_ignoreAnimatedItems.Add(wi.Id);
							return wi;
						}
					}
				}
			}

			return null;
		}

		private WorldItem BestAnimateWeaponTarget(int maxLevel)
		{
			var worldItems = LokiPoe.ObjectManager.GetObjectsByType<WorldItem>()
				.Where(wi => !_ignoreAnimatedItems.Contains(wi.Id) && wi.Distance < 30)
				.OrderBy(wi => wi.Distance);
			foreach (var wi in worldItems)
			{
				var item = wi.Item;
				if (item.IsIdentified &&
					item.RequiredLevel <= maxLevel &&
					!item.IsChromatic &&
					item.SocketCount < 5 &&
					item.MaxLinkCount < 5 &&
					item.Rarity <= Rarity.Magic &&
					(item.IsClawType || item.IsOneHandAxeType || item.IsOneHandMaceType || item.IsOneHandSwordType ||
					item.IsOneHandThrustingSwordType || item.IsTwoHandAxeType || item.IsTwoHandMaceType ||
					item.IsTwoHandSwordType || item.IsDaggerType || item.IsStaffType))
				{
					_ignoreAnimatedItems.Add(wi.Id);
					return wi;
				}
			}
			return null;
		}

		private Monster BestDeadTarget
		{
			get
			{
				var myPos = LokiPoe.Me.Position;
				return LokiPoe.ObjectManager.GetObjectsByType<Monster>()
					.Where(
						m =>
							m.Distance < 30 && m.IsActiveDead && m.Rarity != Rarity.Unique && m.CorpseUsable &&
							ExilePather.PathDistance(myPos, m.Position, true, !OldRoutineSettings.Instance.LeaveFrame) < 30)
					.OrderBy(m => m.Distance).FirstOrDefault();
			}
		}

		private async Task<bool> CombatLogicEnd()
		{
			await EnableAlwaysHiglight();

			return false;
		}

		private async Task<bool> HandleShrines()
		{
			// TODO: Shrines need speical CR logic, because it's now the CRs responsibility for handling all combaat situations,
			// and shrines are now considered a combat situation due their nature.

			// Check for any active shrines.
			var shrines =
				LokiPoe.ObjectManager.Objects.OfType<Shrine>()
					.Where(s => !s.IsDeactivated && s.Distance < 50)
					.OrderBy(s => s.Distance)
					.ToList();

			if (!shrines.Any())
				return false;

			// For now, just take the first shrine found.

			var shrine = shrines[0];

			// Handle Skeletal Shrine in a special way, or handle priority between multiple shrines at the same time.
			var skellyOverride = shrine.ShrineId == "Skeletons";

			// Try and only move to touch it when we have a somewhat navigable path.
			if ((Utility.NumberOfMobsBetween(LokiPoe.Me, shrine, 5, true) < 5 &&
				Utility.NumberOfMobsNear(LokiPoe.Me, 20) < 3) || skellyOverride)
			{
				Log.DebugFormat("[HandleShrines] Now moving towards the Shrine {0}.", shrine.Id);

				var myPos = LokiPoe.Me.Position;

				var pos = ExilePather.WalkablePositionFor(shrine, 10, false, !OldRoutineSettings.Instance.LeaveFrame);

				// We need to filter out based on pathfinding, since otherwise, a large gap will lockup the bot.
				var pathDistance = ExilePather.PathDistance(myPos, pos, true, !OldRoutineSettings.Instance.LeaveFrame);
				if (pathDistance > 50)
				{
					return false;
				}

				var canSee = ExilePather.CanObjectSee(LokiPoe.Me, pos, !OldRoutineSettings.Instance.LeaveFrame);
				var inDistance = myPos.Distance(pos) < 20;
				if (canSee && inDistance)
				{
					Log.DebugFormat("[HandleShrines] Now attempting to interact with the Shrine {0}.", shrine.Id);

					await Coroutines.FinishCurrentAction();

					await Coroutines.InteractWith(shrine);

					await Coroutine.Sleep(500);
				}
				else
				{
					Log.DebugFormat("[HandleShrines] Moving towards {0}. [canSee: {1} | inDistance: {2}]", pos, canSee,
						inDistance);
					if (!PlayerMover.MoveTowards(pos))
					{
						Log.ErrorFormat("[HandleShrines] MoveTowards failed for {0}.", pos);
					}
				}

				return true;
			}

			return false;
		}

		private bool _needsToDisableAlwaysHighlight;

		// This logic is now CR specific, because Strongbox gui labels interfere with targeting,
		// but not general movement using Move only.
		private async Task DisableAlwaysHiglight()
		{
			if (_needsToDisableAlwaysHighlight && LokiPoe.InGameState.IsAlwaysHighlightEnabled)
			{
				Log.InfoFormat("[DisableAlwaysHiglight] Now disabling Always Highlight to avoid skill use issues.");
				LokiPoe.Input.PressKey(LokiPoe.Input.Binding.highlight_toggle);
				await Coroutine.Sleep(16);
			}
		}

		// This logic is now CR specific, because Strongbox gui labels interfere with targeting,
		// but not general movement using Move only.
		private async Task EnableAlwaysHiglight()
		{
			if (!LokiPoe.InGameState.IsAlwaysHighlightEnabled)
			{
				Log.InfoFormat("[EnableAlwaysHiglight] Now enabling Always Highlight.");
				LokiPoe.Input.PressKey(LokiPoe.Input.Binding.highlight_toggle);
				await Coroutine.Sleep(16);
			}
		}

		private int EnsurceCast(int slot)
		{
			if (slot == -1)
				return slot;

			var slotSkill = LokiPoe.InGameState.SkillBarPanel.Slot(slot);
			if (slotSkill == null || !slotSkill.CanUse())
			{
				return -1;
			}

			return slot;
		}

		#region Override of Object

		/// <summary>Returns a string that represents the current object.</summary>
		/// <returns>A string that represents the current object.</returns>
		public override string ToString()
		{
			return Name + ": " + Description;
		}

		#endregion
	}
}
