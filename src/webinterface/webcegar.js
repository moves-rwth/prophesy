// webcegar settings
var currentResult = "";
var pmc = ""
var sat = ""
var sampler = ""

function fillSelect(select, data, selected) {
    select.empty()
    for (var key in data) {
        select.append($('<option>', {
            value: key,
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
    });
}

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
    });
}

function getSamples() {
    doJSON("../samples", function(result) {
        readSamples(result.data);
        plotSamples();
    });
}

function getConstraints() {
    doJSON("../constraints", function(result) {
        readConstraints(result.data);
        plotSamples();
    });
}

function listEnv() {
    doJSON("../environments", function(result) {
        var pmcTools = $("#mctools");
        fillSelect(pmcTools, result.data.pmc, pmc);

        var samplers = $("#samplers");
        fillSelect(samplers, result.data.samplers, sat);

        var smtSolvers = $("#satsolvers");
        fillSelect(smtSolvers, result.data.sat, sampler);
        
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
