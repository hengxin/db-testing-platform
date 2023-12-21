import request from '@/utils/request'

const historyCountUrl = "/history_count"

export function get_history_count() {
    return request.get(historyCountUrl)
}

const bugCountUrl = "/bug_count"

export function get_bug_count() {
    return request.get(bugCountUrl)
}

const runUrl = "/run"

export function run(params) {
    return request.post(runUrl, params)
}

const bugListUrl = "/bug_list"

export function get_bug_list() {
    return request.get(bugListUrl)
}

const runListUrl = "/run_list"

export function get_run_list() {
    return request.get(runListUrl)
}

const downloadUrl = "/download/"

export function download_bug(bug_id) {
    return request.get(downloadUrl + bug_id, {
        responseType: 'blob'
    })
}

const downloadRunUrl = "/download_run/"

export function download_run(run_id) {
    return request.get(downloadRunUrl + run_id, {
        responseType: 'blob'
    })
}

const viewUrl = "/view/"

export function get_graph(bug_id) {
    return request.get(viewUrl + bug_id)
}