document.addEventListener("DOMContentLoaded", function() {
  renderMathInElement(document.body, {
    // customised options
    // • auto-render specific keys, e.g.:
    delimiters: [
      {left: '$$', right: '$$', display: true},
      {left: '`', right: '`', display: false},
      {left: '\\(', right: '\\)', display: false},
      {left: '\\[', right: '\\]', display: true}
    ],
    // • rendering keys, e.g.:
    throwOnError : false
  });
});


function timeToSeconds(timeString) {
  // Split the time string into hours, minutes, and seconds
  const [hours, minutes, seconds] = timeString.split(':').map(Number);
  
  // Calculate the total time in seconds
  const totalTimeInSeconds = hours * 3600 + minutes * 60 + seconds;
  
  return totalTimeInSeconds;
}

// vid_helper("[[this]]", "[[youtubeid]]", "[[start]]", "[[end]]");
function vid_helper(elid, youtubeid, start, end) {
  mydiv = document.getElementById(elid);
  console.log("mydiv has element id: " + elid);
  myframe = mydiv.querySelector("iframe");
  console.log("myframe", myframe);
  
  var st = timeToSeconds(start);
  var et = timeToSeconds(end);

  console.log("vid_helper got youtubeid: " + youtubeid);
  var u = [
    `https://www.youtube.com/embed/`, youtubeid,
    `?autoplay=0`,
    `&enablejsapi=1`,
    `&start=` + st,
    `&end=` + et,
  ].join("");

  
  console.log(u)
  myframe.src=u  
}

function youtubeSeekTo(iframeId, startTime) {
  var player;
  function onYouTubeIframeAPIReady() {
    player = new YT.Player(iframeId, {
      events: {
        'onReady': onPlayerReady,
        'onStateChange': onPlayerStateChange
      }
    });
  }
  
  function onPlayerReady() {
    console.log("hey Im ready");
    player.seekTo(startTime);
    player.pauseVideo();
  }

  function onPlayerStateChange() {
    console.log("my state changed");
  }
}

var _unit = 1;
var _seq = 1;
var _page = 1;
var _def = 0;
var _prob = 0;

function cur_def() {
  _def += 1;
  return ""+ _unit + "." + _seq + "." +_def + ".";
}

function cur_prob() {
  _prob += 1;
  return ""+ _unit + "." + _seq + "." +_prob + ".";
}


// https://stackoverflow.com/a/819455/98770
function resizeIFrameToFitContent( iFrame, call_depth) {
  let h = iFrame.contentWindow.document.body.scrollHeight;
  
  if (h < 100) {
    setTimeout(function() {
      resizeIFrameToFitContent(iFrame, call_depth);
    }, 1000);
  } else {
    iFrame.height = iFrame.contentWindow.document.body.scrollHeight + 400;
  }
}

function addProofIframeListener(frameId) {
  window.addEventListener('DOMContentLoaded', function(e) {
    var iFrame = document.getElementById(frameId );
    resizeIFrameToFitContent( iFrame, 0);
  } );
}

function sidebar_section_links() {
  window.addEventListener('DOMContentLoaded', function(e) {  
    let pages = document.getElementsByClassName("page");
    if (pages[0]) {
      let page = pages[0];
      console.log(page.title)
    }
  });
}


function adjust_iframe_height(frameId) {
  // Function to adjust iframe size
  function resizeIframe() {
    const iframe = document.getElementById(frameId);
    if (iframe) {
      if (iframe.contentWindow) {
        const iframeDocument = iframe.contentWindow.document;
        if (iframeDocument) {
          const contentHeight = iframeDocument.documentElement.scrollHeight;
          iframe.style.height = contentHeight + 'px';
        }
      }
    }
  }  
  // Adjust size when iframe content is loaded
  const iframe = document.getElementById(frameId);
  console.log("my leancode iframe's id is: " + iframe)
  iframe.addEventListener('load', resizeIframe);
}
