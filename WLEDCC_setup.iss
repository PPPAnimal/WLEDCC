#define MyAppName "WLED Command Center"
;#define MyAppVersion "4.5.0"
#define MyAppPublisher "SullySSignS"
#define MyAppURL "https://www.sullyssigns.ca"
#define MyAppExeName "WLEDCC.exe"
#define MyAppDataFolder "WLEDCC"
#define MyAppIconFile "wledccicon.ico"

[Setup]
AppId={{A1B2C3D4-E5F6-7890-ABCD-EF1234567890}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
AppPublisherURL={#MyAppURL}
AppSupportURL={#MyAppURL}
DefaultDirName={autopf}\{#MyAppName}
DefaultGroupName={#MyAppName}
AllowNoIcons=yes
PrivilegesRequired=admin
PrivilegesRequiredOverridesAllowed=commandline
UsedUserAreasWarning=no
OutputDir=.
OutputBaseFilename=WLEDCC_Setup_v{#MyAppVersion}
Compression=lzma
SolidCompression=yes
WizardStyle=modern
SetupIconFile=wledccicon.ico
UninstallDisplayName={#MyAppName}

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[Tasks]
Name: "desktopicon"; Description: "{cm:CreateDesktopIcon}"; GroupDescription: "{cm:AdditionalIcons}"; Flags: unchecked
Name: "startmenuicon"; Description: "Create a Start Menu shortcut"; GroupDescription: "{cm:AdditionalIcons}"; Flags: checkedonce

[Files]
Source: "version.txt"; DestDir: "{app}"; Flags: ignoreversion
Source: "dist\WLEDCC.exe"; DestDir: "{app}"; Flags: ignoreversion
Source: "wledccicon.ico"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; IconFilename: "{app}\{#MyAppIconFile}"
Name: "{group}\Uninstall {#MyAppName}"; Filename: "{uninstallexe}"
Name: "{commondesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; IconFilename: "{app}\{#MyAppIconFile}"; Tasks: desktopicon

[Dirs]
Name: "{userappdata}\{#MyAppDataFolder}"

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "{cm:LaunchProgram,{#StringChange(MyAppName, '&', '&&')}}"; Flags: nowait postinstall skipifsilent

[Code]
procedure CurUninstallStepChanged(CurUninstallStep: TUninstallStep);
var
  ProfilesDir: string;
  FindRec: TFindRec;
  DataDir: string;
  DeleteData: Boolean;
begin
  if CurUninstallStep = usUninstall then
  begin
    DeleteData := MsgBox(
      'Do you want to delete all saved settings, scenes, and log files?' + #13#10 +
      '(AppData\Roaming\WLEDCC)' + #13#10 + #13#10 +
      'Click Yes to remove everything, No to keep your settings.',
      mbConfirmation, MB_YESNO) = IDYES;

    if DeleteData then
    begin
      ProfilesDir := ExpandConstant('{userappdata}');
      DataDir := ProfilesDir + '\{#MyAppDataFolder}';
      if DirExists(DataDir) then
        DelTree(DataDir, True, True, True);
      ProfilesDir := GetEnv('SystemDrive') + '\Users';
      if FindFirst(ProfilesDir + '\*', FindRec) then
      begin
        repeat
          if (FindRec.Attributes and FILE_ATTRIBUTE_DIRECTORY <> 0) and
             (FindRec.Name <> '.') and (FindRec.Name <> '..') then
          begin
            DataDir := ProfilesDir + '\' + FindRec.Name +
                       '\AppData\Roaming\{#MyAppDataFolder}';
            if DirExists(DataDir) then
              DelTree(DataDir, True, True, True);
          end;
        until not FindNext(FindRec);
        FindClose(FindRec);
      end;
    end;
  end;
end;
