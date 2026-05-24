#define MyAppName "WLED Command Center"
#define MyAppPublisher "SullySSignS"
#define MyAppURL "https://www.sullyssigns.ca"
#define MyAppExeName "WLEDCC.exe"
#define MyAppSAExeName "SA.exe"
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
OutputDir=D:\Projects\WLEDCC
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
Name: "desktopicon_sa"; Description: "Create a Desktop shortcut for Spectrum Analyzer"; GroupDescription: "{cm:AdditionalIcons}"; Flags: unchecked
Name: "startmenuicon"; Description: "Create a Start Menu shortcut"; GroupDescription: "{cm:AdditionalIcons}"; Flags: checkedonce

[Files]
; Grab the entire folder created by PyInstaller
Source: "dist\WLEDCC_Shared\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

; Additional root files
Source: "version.txt"; DestDir: "{app}"; Flags: ignoreversion
Source: "LICENSE"; DestDir: "{app}"; Flags: ignoreversion
Source: "Manual.txt"; DestDir: "{app}"; Flags: ignoreversion
Source: "CHANGELOG.md"; DestDir: "{app}"; Flags: ignoreversion
Source: "wledccicon.ico"; DestDir: "{app}"; Flags: ignoreversion
Source: "*.jpg"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; IconFilename: "{app}\{#MyAppIconFile}"
Name: "{group}\Spectrum Analyzer"; Filename: "{app}\{#MyAppSAExeName}"; IconFilename: "{app}\{#MyAppIconFile}"
Name: "{group}\Uninstall {#MyAppName}"; Filename: "{uninstallexe}"
Name: "{commondesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; IconFilename: "{app}\{#MyAppIconFile}"; Tasks: desktopicon
Name: "{commondesktop}\WLEDCC Spectrum Analyzer"; Filename: "{app}\{#MyAppSAExeName}"; IconFilename: "{app}\{#MyAppIconFile}"; Tasks: desktopicon_sa

[Dirs]
Name: "{userappdata}\{#MyAppDataFolder}"

[InstallDelete]
Type: files; Name: "{app}\Brushed Metal.jpg"
Type: files; Name: "{app}\Nebula Space.jpg"
Type: files; Name: "{app}\Planets Space.jpg"
Type: files; Name: "{app}\Retro Blue.jpg"
Type: files; Name: "{app}\Retro Yellow.jpg"

[Code]
procedure CurUninstallStepChanged(CurUninstallStep: TUninstallStep);
var
  ProfilesDir: string;
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
    end;
  end;
end;