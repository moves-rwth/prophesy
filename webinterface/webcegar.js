// webcegar settings
var currentResult = "";
var pmc = ""
var sat = ""
var sampler = ""

function fillSelect(select, data, selected) {
    select.empty()
    for (var key in data) {
        select.append($('<option>', {
            value: data[key],
            text: data[key]
        }));
    }
    if (selected !== null) {
        select.val(selected);
    }
}

function listAvailableResults() {
    doJSON("../results", function(result) {
        var availableFiles = $("#result-files");
        fillSelect(availableFiles, result.data, currentResult);

        getCurrentResult();
    });
}

// Update display to show the active result information
function getResultData(name) {
    doJSON("../results/"+name, function(result) {
        $("#info_ratfunc").html(result.data);
    }, function() {
        $("#info_ratfunc").text("Failed to retrieve data");
    });
}

function getCurrentResult() {
    doJSON("../currentResult", function(result) {
        currentResult = result.data;
        $("#result-files").val(currentResult);
        getResultData(currentResult);
    }, function() {
        currentResult = "";
    });
}

function setCurrentResult(file) {
    var formData = new FormData();
    formData.append('name', file);
    doAjax({
        url: '../currentResult',
        type: 'POST',
        // Form data
        data: formData,
        //Options to tell jQuery not to process data or worry about content-type.
        cache: false,
        contentType: false,
        processData: false
    }, function(result) {
        currentResult = file;
        getResultData(currentResult);
    });
}

function getThreshold() {
    doJSON("../threshold", function(result) {
        threshold = result.data;
        threshold = Number(threshold).toFixed(3);
        $('#thresholdSlider').val(threshold);
        $("#thresvalue").text(threshold);
        plotSamples();
    });
}

// -------------------------------------- Getter and Setter for expert Config


/* TODO: Create one generic Setter
** THIS ONE IS JUST HOW IT MAY BE LOOK LIKE
**/
function setConfig(section, key, data){
    var formData = new FormData();
    formData.append('data',$("#"+data).val());
    doAjax({
        url: '../config/'+section+'/'+key,
        type: 'POST',
        data: formData,
        cache: false,
        contentType: false,
        processData: false
    });
}

function getConfig(section, key){
    doJSON("../config/"+section+"/"+key, function(result) {
        return result.data;
    });
}
// -----------------------------------------

function getStormConfig(){
    doJSON("../config/external_tools/storm", function(result) {
        cfgStorm = result.data;
        $("#stormpath").val(cfgStorm);
        $("#stormpath").text(cfgStorm);
    });
}

function setStormPath(){
    var formData = new FormData();
    formData.append('data',$("#stormpath").val());
    doAjax({
        url: '../config/external_tools/storm',
        type: 'POST',
        data: formData,
        cache: false,
        contentType: false,
        processData: false
    });
}

function setZ3Path(){
    var formData = new FormData();
    formData.append('data',$("#z3path").val());
    doAjax({
        url: '../config/external_tools/z3',
        type: 'POST',
        data: formData,
        cache: false,
        contentType: false,
        processData: false
    });
}

function getPrecisionConfig(){
    doJSON("../config/constraints/precision", function(result) {
        cfgPrec = result.data;
        $("#precision").val(cfgPrec);
    });
}

function setPrecision(){
    var formData = new FormData();
    formData.append('data',$("#precision").val());
    doAjax({
        url: '../config/constraints/precision',
        type: 'POST',
        data: formData,
        cache: false,
        contentType: false,
        processData: false
    });
}

function getZ3Config(){
    doJSON("../config/external_tools/z3", function(result) {
        cfgZ3 = result.data;
        $("#z3path").val(cfgZ3);
        $("#z3path").text(cfgZ3);
    });
}
// ------------------------------------ End of Getter/Setter for Expert Config

function setThreshold(threshold) {
    var formData = new FormData();
    formData.append('threshold', threshold);
    doAjax({
        url: '../threshold',
        type: 'POST',
        // Form data
        data: formData,
        //Options to tell jQuery not to process data or worry about content-type.
        cache: false,
        contentType: false,
        processData: false
    }, function(result) {
        safe_constraints = [];
        bad_constraints = [];
        plotSamples();
    });
}

function getSamples() {
    doJSON("../samples", function(result) {
        readSamples(result.data);
        plotSamples();
    });
}

function clearSamples() {
    doAjax({
        url: '../samples',
        type: 'DELETE',
    }, function(result) {
        samples = [];
        plotSamples();
    });
}

function getConstraints() {
    doJSON("../constraints", function(result) {
        readConstraints(result.data);
        plotSamples();
    });
}

function clearConstraints() {
    doAjax({
        url: '../constraints',
        type: 'DELETE',
    }, function(result) {
        safe_constraints = [];
        bad_constraints = [];
        plotSamples();
    });
}

function listEnv() {
    doJSON("../environments", function(result) {
        var pmcTools = $("#mctools");
        fillSelect(pmcTools, result.data.pmc, pmc);

        var samplers = $("#samplers");
        fillSelect(samplers, result.data.samplers, sampler);

        var smtSolvers = $("#satsolvers");
        fillSelect(smtSolvers, result.data.sat, sat);

        getEnv();
    });
}

function setEnv() {
    var formData = new FormData();
    formData.append('pmc', $("#mctools").val());
    formData.append('sampler', $("#samplers").val());
    formData.append('sat', $("#satsolvers").val());
    doAjax({
        url: '../environment',
        type: 'POST',
        // Form data
        data: formData,
        //Options to tell jQuery not to process data or worry about content-type.
        cache: false,
        contentType: false,
        processData: false
    });
}

function getEnv() {
    doJSON("../environment", function(result) {
        pmc = result.data.pmc;
        $("#mctools").val(pmc);
        sampler = result.data.sampler;
        $("#samplers").val(sampler);
        sat = result.data.sat;
        $("#satsolvers").val(sat);
    });
}

function listPRISMFiles() {
    doJSON("../uploadPrism", function(result){
        var hSelect = $("#uploaded-prism-files");
        var files = result.data.prism;
        hSelect.empty();
        for (var filename in files) {
            hSelect.append($('<option>', {
                value: filename,
                text: filename
            }));
        }
    });
}

function listPCTLFiles() {
    doJSON("../uploadPctl", function(result){
        var hSelect = $("#uploaded-pctl-files");
        var files = result.data.pctl;
        hSelect.empty();
        for (var filename in files){
            hSelect.append($('<option>', {
                value: filename,
                text: filename
                }));
            }
        })
}

function listAvailableFiles(){
    listPRISMFiles();
    isBusy=false;
    listPCTLFiles();
}

function listFilesForManager(){
    doJSON("../uploadPrism", function(result){
        var list = $("#prism");
        var files = result.data.prism;
        list.empty();
        for (var filename in files) {
            list.append($('<li>', {
                value: filename,
                text: filename
            }));
        }
    });
    doJSON("../uploadPctl", function(result){
        var list = $("#pctl");
        var files = result.data.pctl;
        list.empty();
        for (var filename in files) {
            list.append($('<li>', {
                value: filename,
                text: filename
            }));
        }
    });
    doJSON("../results", function(result) {
        var list = $("#result-files");
        var files = result.data
        list.empty();
        for (var filename in result.data){
            list.append($('<li>', {
                value: filename,
                text: filename
            }));
        }
        getCurrentResult();
    });
}