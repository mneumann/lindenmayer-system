all:
	cargo run --example abop_1_9 15
	cargo run --example dragon_curve 14
	cargo run --example fractal_plant 6
	cargo run --example koch_curve 5
	cargo run --example sierpinski 9
	convert -resize 800x abop_1_9_15.eps abop_1_9_15.gif
	convert -resize 800x dragon_14.eps dragon_14.gif 
	convert -resize 800x plant_06.eps plant_06.gif 
	convert -resize 800x koch_05.eps koch_05.gif 
	convert -resize 800x sierpinski_09.eps sierpinski_09.gif 
