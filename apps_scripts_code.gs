function onOpen() {
  SpreadsheetApp.getUi()
    .createMenu('Fantasy Tools')
    .addItem('Run Refresh', 'runGitHubRefresh')
    .addItem('Show Last Update Tab', 'showLastUpdateTab')
    .addToUi();
}

function runGitHubRefresh() {
  const props = PropertiesService.getScriptProperties();

  const owner = props.getProperty('GITHUB_OWNER') || 'deanrillo123-lgtm';
  const repo = props.getProperty('GITHUB_REPO') || 'baseball-sheet-refresh';
  const workflowFile = props.getProperty('GITHUB_WORKFLOW_FILE') || 'baseball-sheet-refresh.yml';
  const branch = props.getProperty('GITHUB_BRANCH') || 'main';
  const token = props.getProperty('GITHUB_TOKEN');

  if (!token) {
    SpreadsheetApp.getUi().alert(
      'Missing GITHUB_TOKEN in Apps Script > Project Settings > Script Properties.'
    );
    return;
  }

  const url =
    'https://api.github.com/repos/' +
    owner + '/' + repo +
    '/actions/workflows/' + encodeURIComponent(workflowFile) +
    '/dispatches';

  const payload = {
    ref: branch,
    inputs: {
      refresh_type: 'apps_script'
    }
  };

  const options = {
    method: 'post',
    contentType: 'application/json',
    headers: {
      Authorization: 'Bearer ' + token,
      Accept: 'application/vnd.github+json',
      'X-GitHub-Api-Version': '2022-11-28'
    },
    payload: JSON.stringify(payload),
    muteHttpExceptions: true
  };

  const response = UrlFetchApp.fetch(url, options);
  const code = response.getResponseCode();
  const body = response.getContentText();

  if (code >= 200 && code < 300) {
    SpreadsheetApp.getUi().alert('GitHub refresh triggered successfully.');
  } else {
    SpreadsheetApp.getUi().alert('GitHub refresh failed.\nHTTP ' + code + '\n' + body);
  }
}

function showLastUpdateTab() {
  const ss = SpreadsheetApp.getActiveSpreadsheet();
  const sheet = ss.getSheetByName('last_update');
  if (sheet) ss.setActiveSheet(sheet);
}
