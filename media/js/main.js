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
  if (!timeString) return 0; // Handle empty or null timeString

  const parts = timeString.split(':');
  if (parts.length === 1) {
    // Assume it's just seconds (e.g., "30")
    const seconds = parseInt(parts[0], 10);
    if (isNaN(seconds)) {
      console.error("Invalid time format. Use minutes:seconds (e.g., '1:30') or just seconds (e.g., '30')");
      return 0;
    }
    return seconds;
  } else if (parts.length === 2) {
    // minutes:seconds format (e.g., "1:30")
    const minutes = parseInt(parts[0], 10);
    const seconds = parseInt(parts[1], 10);

    if (isNaN(minutes) || isNaN(seconds)) {
      console.error("Invalid time format. Use minutes:seconds (e.g., '1:30')");
      return 0;
    }
    return (minutes * 60) + seconds;
  } else {
    console.error("Invalid time format. Use minutes:seconds (e.g., '1:30') or just seconds (e.g., '30')");
    return 0; // Or handle error as needed
  }
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


// function timeToSeconds(timeString) {
//   // Split the time string into hours, minutes, and seconds
//   const [hours, minutes, seconds] = timeString.split(':').map(Number);
  
//   // Calculate the total time in seconds
//   const totalTimeInSeconds = hours * 3600 + minutes * 60 + seconds;
  
//   return totalTimeInSeconds;
// }

// // vid_helper("[[this]]", "[[youtubeid]]", "[[start]]", "[[end]]");
// function vid_helper(elid, youtubeid, start, end) {
//   mydiv = document.getElementById(elid);
//   console.log("mydiv has element id: " + elid);
//   myframe = mydiv.querySelector("iframe");
//   console.log("myframe", myframe);
  
//   var st = timeToSeconds(start);
//   var et = timeToSeconds(end);

//   console.log("vid_helper got youtubeid: " + youtubeid);
//   var u = [
//     `https://www.youtube.com/embed/`, youtubeid,
//     `?autoplay=0`,
//     `&enablejsapi=1`,
//     `&start=` + st,
//     `&end=` + et,
//   ].join("");

  
//   console.log(u)
//   myframe.src=u  
// }

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


function copyText(id) {
  console.log(id);
  const content = document.getElementById(id);
  const range = document.createRange();
  range.selectNode(content);
  window.getSelection().removeAllRanges();
  window.getSelection().addRange(range);
  
  try {
    document.execCommand('copy');
    content.classList.add('copied');  // Add the 'copied' class to trigger the animation
    setTimeout(() => {
      content.classList.remove('copied'); // Remove it after the animation finishes
    }, 500); // Duration of the animation (2 seconds)
  } catch (err) {
    alert('Failed to copy text.');
  }

  window.getSelection().removeAllRanges();
}


