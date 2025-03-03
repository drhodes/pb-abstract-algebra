import * as THREE from 'https://cdn.jsdelivr.net/npm/three@0.173.0/build/three.module.js';
import { GLTFLoader } from 'https://cdn.jsdelivr.net/npm/three@0.173.0/examples/jsm/loaders/GLTFLoader.js';
import { Tween } from 'https://cdn.skypack.dev/@tweenjs/tween.js';


const pi=3.1415926;

const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(75, 1, 0.1, 1000);
const renderer = new THREE.WebGLRenderer();

renderer.setSize(350, 350);
ctx.appendChild(renderer.domElement);

// Load GLB model (ensure you have a cube.glb file available)
const loader = new GLTFLoader();
let cube;
let tweenx;

loader.load(
  '../media/mathlets/cube-group/assets/cube.glb',  
  (gltf) => {
    const model = gltf.scene;
    cube = model;
    scene.add(model);
    
    // Optionally, adjust scale/position of the model
    model.scale.set(1, 1, 1);
    model.position.set(0, 0, 0);
    
    tweenx = new Tween(cube.rotation);
    tweenx.to({x:pi}, 500);
    tweenx.start();
    animate();
    tweenx.onUpdate(function (obj) {
    });


  },
  undefined,  // Progress callback
  (error) => {  // Error callback
    console.error('An error occurred while loading the model:', error);
  }
);

camera.position.z = 2;
camera.position.x = 2;
camera.position.y = 3;

const light = new THREE.DirectionalLight(0xffffff, 1);
light.position.set(1, 1, 1).normalize();
scene.add(light);

const ambientLight = new THREE.AmbientLight(0xffffff, 3);
scene.add(ambientLight);

camera.lookAt(0,0,0);
renderer.setClearColor(new THREE.Color(0xFFFFFF)); 

function animate() {
  requestAnimationFrame(animate);
  tweenx.update();
  renderer.render(scene, camera);  
}
