NewTrainingSquare.py Requires:
- BigIsland_CustomVegetationAreas (Kanoas island sections layer)
- CAH_LandCover (JPs veg areas layer) [/X:/PROJECTS_2/Big_Island/ChangeHI_Trees/Dry_Forest/Data/Vector/Tiles/CAH_LandCover.gpkg]
- training_squares* (gpkg with specific attribute table that updates upon running) *must be set to edit mode* {100mx100m square that extracts attribute info from other layers^^}

CanopyTypeLabeler2.py Requires:
- CHM (Be sure to rename it 'chm')
- training_canopies* (gpkg with specific attribute table that updates upon running) *must be set to edit mode* {populates specific attributes upon run: training square fid, apex height, meters squares, the mode the script was in, the ortho it was placed on, species of tree is already labeled; OR null if hand drawn polygon}

CanopyCrownLabeler.py Requires: 
- CHM (Be sure to rename it 'chm')
- training_canopies* (gpkg with specific attribute table that updates upon running) *must be set to edit mode*
*Same tool as 'CanopyTypeLabeler2.py'^ but with more parameters and for different forest structure and tightness*

PolygonsWithinSquare3.py Requires:
- training_squares*.gpkg
- training_canopies*.gpkg
- CHM (Be sure to rename it 'chm')

ApexDetector.py Requires:
- training_squares*.gpkg
- training_apexes (gpkg with specific attribute table that updates upon running) *must be in edit mode* {layer that attempts to find all the apexes in a given area)
- CHM (Be sure to rename it 'chm'}

**CanopyTypeLabeler2.py, PolygonsWithinSquare3.py, & ApexDetector.py**
Have capability of DENSE, MIXED, & SPARSE for input which represent different types of forest. DENSE seems to work best overall because it is more selective with what it keeps but the other versions can be usefully for loosening parameters to capture more of a canopy.

**CanopyCrownLabeler.py**
Goes deeper into the types of forest and allows the user to set a value between 1-21; where 1 is the loosest setting and 21 is the tightest setting.