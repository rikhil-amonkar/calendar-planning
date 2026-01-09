problem.addConstraint(lambda name, genre, h=house: not (name == "Arnold") or (genre == "mystery"), 
                     [f"name_{h}", f"genre_{h}"])