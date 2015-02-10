var currentResult = "";

function listAvailableResults() {
    doJSON("../listAvailableResults/", function(result) {
        var availableFiles = $("#result-files");
        availableFiles.empty();
        for (var key in result.data.results) {
            var resname = result.data.results[key];
            option = availableFiles.append($("<option />").val(resname).text(resname));
            if (resname == currentResult) {
                option.prop("selected", true);
            }
        }
    });
}

// Update display to show the active result information
function getResultData(name) {
    doJSON("../getResultData/"+name, function(result) {
        $("#info_ratfunc").text(result.data.result_data);
    }, function() {
        $("#info_ratfunc").text("Failed to retrieve data");
    });
}

function getCurrentResult() {
    doJSON("../getCurrentResult/", function(result) {
        currentResult = result.data.result;
        getResultData(currentResult);
    }, function() {
        currentResult = "";
    });
}

function setCurrentResult(file) {
    doJSON("../setCurrentResult/"+file, function(result) {
        $("#info_ratfunc").text(result.data.result.ratfunc);
        currentResult = file;
    }, function() {
        $("#info_ratfunc").text("Not loaded");
    });
}

function getThreshold() {
    doJSON("../getThreshold/", function(result) {
        threshold = result.data.threshold;
        $('#thresholdSlider').val(threshold*1000);
        $("#thresvalue").text(threshold);
    });
}

function setThreshold(threshold) {
    doJSON("../setThreshold/"+threshold);
}

function getSamples() {
    doJSON("../getSamples", function(result) {
        readSamples(result.data);
        plotSamples();
    });
}
