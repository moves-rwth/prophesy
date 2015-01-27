var currentResult = "";

function listAvailableResults() {
    setBusy(true);
    $.getJSON("../listAvailableResults/", function(result) {
        if (result.status == "ok") {
            var availableFiles = $("#result-files");
            availableFiles.empty();
            for (var key in result.data.results) {
                var resname = result.data.results[key];
                option = availableFiles.append($("<option />").val(resname).text(resname));
                if (resname == currentResult) {
                    option.prop("selected", true);
                }
            };
        }
    }).fail(function(jqXHR) {
        //result = $.parseJSON(jqXHR.responseText);
        //alert("Ajax Failure: " + result.reason);
    }).always(function() {setBusy(false);});
}

// Update display to show the active result information
function getResultData(name) {
    setBusy(true);
    function fail() {
        $("#info_ratfunc").text("Failed to retrieve data");
    };
    
    $.getJSON("../getResultData/"+name, function(result) {
        if (result.status != "ok") {
            fail();
        } else {
            $("#info_ratfunc").text(result.data.result_data);
        }
    }).fail(function(jqXHR) {
        //result = $.parseJSON(jqXHR.responseText);
        //alert("Failed getting result data: " + result.reason);
        fail();
    }).always(function() {setBusy(false);});
}

function getCurrentResult() {
    setBusy(true);
    $.getJSON("../getCurrentResult/", function(result) {
        if (result.status != "ok") {
            currentResult = "";
        } else {
            currentResult = result.data.result;
            getResultData(currentResult);
        }
    }).fail(function(jqXHR) {
        currentResult = "";
    }).always(function() {setBusy(false);});
}

function setCurrentResult(file) {
    setBusy(true);
    $.getJSON("../setCurrentResult/"+file, function(result) {
        if (result.status == "ok") {
            $("#info_ratfunc").text(result.data.result.ratfunc);
            currentResult = file;
        }
    }).fail(function(jqXHR) {
        //result = $.parseJSON(jqXHR.responseText);
        //alert("Failed getting result data: " + result.reason);
        $("#info_ratfunc").text("Not loaded");
    }).always(function() {setBusy(false);});
}

function getThreshold() {
    setBusy(true);
    $.getJSON("../getThreshold/", function(result) {
        if (result.status == "ok") {
            threshold = result.data.threshold;
            $('#thresholdSlider').val(threshold*1000);
            $("#thresvalue").text(threshold);
        }
    }).always(function() {setBusy(false);});
}

function setThreshold(threshold) {
    setBusy(true);
    $.getJSON("../setThreshold/"+threshold)
    .always(function() {setBusy(false);});
}

function getSamples() {
    setBusy(true);
    $.getJSON("../getSamples", function(result) {
        if (result.status == "ok") {
            readSamples(result.data);
            plotSamples();
        }
    }).always(function() {setBusy(false);});
}