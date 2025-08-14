#!/usr/bin/env python3
import itertools
import json

def main():
    # There are 6 houses (index 0 to 5 corresponding to House 1 to House 6)
    # Attributes: "Name" and "Favorite Music"
    # Names: Arnold, Eric, Peter, Alice, Carol, Bob
    # Music: jazz, pop, classical, rock, hip hop, country
    #
    # Fixed information from clues:
    #  - House 2 (index 1) Name is Eric.
    #  - House 3 (index 2) Favorite Music is hip hop.
    #  - House 6 (index 5) Name is Carol and Favorite Music is country.
    #
    # Clues to implement:
    # 1. Bob is directly left of the person who loves jazz.
    # 2. Eric is somewhere to the left of the person who loves hip-hop.
    # 3. Carol is in the sixth house.
    # 4. Eric and the person who loves hip-hop are next to each other.
    # 5. The person who loves country music is Carol.
    # 6. Arnold is not in the fifth house.
    # 7. Arnold is somewhere to the right of the person who loves pop.
    # 8. The person who loves pop music is Peter.
    # 9. The person who loves hip-hop music is in the third house.
    # 10. There is one house between Peter and Bob.
    # 11. The person who loves rock music is not in the fifth house.
    
    # All houses will be represented as a dictionary with keys "House", "Name", and "Favorite Music"
    # Fixed assignments:
    #   House index 1: Name = "Eric"
    #   House index 2: Favorite Music = "hip hop"
    #   House index 5: Name = "Carol", Favorite Music = "country"

    # Unknown name positions and available names:
    # Houses with unknown names: index 0, 2, 3, 4
    remaining_names = ["Arnold", "Peter", "Alice", "Bob"]
    unknown_name_indices = [0, 2, 3, 4]
    
    # Unknown music positions and available music:
    # Houses with unknown music: index 0, 1, 3, 4
    remaining_music = ["jazz", "pop", "classical", "rock"]
    unknown_music_indices = [0, 1, 3, 4]
    
    solutions = []
    
    # Permute possible assignments for the unknown names
    for names_perm in itertools.permutations(remaining_names):
        # Initialize houses list
        houses = [{"House": str(i+1), "Name": None, "Favorite Music": None} for i in range(6)]
        
        # Fixed name assignments:
        houses[1]["Name"] = "Eric"
        houses[5]["Name"] = "Carol"
        
        # Assign names based on the permutation to unknown indices
        houses[unknown_name_indices[0]]["Name"] = names_perm[0]  # House 1 (index 0)
        houses[unknown_name_indices[1]]["Name"] = names_perm[1]  # House 3 (index 2)
        houses[unknown_name_indices[2]]["Name"] = names_perm[2]  # House 4 (index 3)
        houses[unknown_name_indices[3]]["Name"] = names_perm[3]  # House 5 (index 4)
        
        # Constraint 6: Arnold is not in the fifth house => House 5 (index 4) must not be Arnold.
        if houses[4]["Name"] == "Arnold":
            continue
        
        # Permute possible assignments for the unknown music values.
        for music_perm in itertools.permutations(remaining_music):
            # Fixed music assignments:
            houses[2]["Favorite Music"] = "hip hop"  # House 3 (index 2)
            houses[5]["Favorite Music"] = "country"    # House 6 (index 5)
            
            # Assign music to unknown music positions:
            # unknown_music_indices are [0, 1, 3, 4] corresponding to houses 1,2,4,5.
            houses[unknown_music_indices[0]]["Favorite Music"] = music_perm[0]  # House 1
            houses[unknown_music_indices[1]]["Favorite Music"] = music_perm[1]  # House 2
            houses[unknown_music_indices[2]]["Favorite Music"] = music_perm[2]  # House 4
            houses[unknown_music_indices[3]]["Favorite Music"] = music_perm[3]  # House 5
            
            # Constraint 11: The person who loves rock is not in the fifth house (index 4).
            if houses[4]["Favorite Music"] == "rock":
                continue
            
            valid = True
            
            # Constraint 8: The person who loves pop music is Peter.
            # This implies that if a house's Favorite Music is "pop", its Name must be "Peter", and vice versa.
            for house in houses:
                if house["Favorite Music"] == "pop" and house["Name"] != "Peter":
                    valid = False
                    break
                if house["Name"] == "Peter" and house["Favorite Music"] != "pop":
                    valid = False
                    break
            if not valid:
                continue
            
            # Constraint 1: Bob is directly left of the person who loves jazz.
            for i in range(6):
                if houses[i]["Name"] == "Bob":
                    # Bob cannot be in the last house because he must be immediately left of someone.
                    if i == 5 or houses[i+1]["Favorite Music"] != "jazz":
                        valid = False
                        break
            if not valid:
                continue
            
            # Constraint 10: There is one house between Peter and Bob.
            index_peter = None
            index_bob = None
            for i, house in enumerate(houses):
                if house["Name"] == "Peter":
                    index_peter = i
                if house["Name"] == "Bob":
                    index_bob = i
            if index_peter is None or index_bob is None or abs(index_peter - index_bob) != 2:
                valid = False
            if not valid:
                continue
            
            # Constraint 7: Arnold is somewhere to the right of the person who loves pop (i.e., Peter).
            index_arnold = None
            for i, house in enumerate(houses):
                if house["Name"] == "Arnold":
                    index_arnold = i
            if index_peter is None or index_arnold is None or not (index_peter < index_arnold):
                valid = False
            if not valid:
                continue
            
            # Constraint 2: Eric is somewhere to the left of the person who loves hip-hop.
            # Constraint 4: Eric and the person who loves hip-hop are next to each other.
            index_eric = None
            index_hiphop = None
            for i, house in enumerate(houses):
                if house["Name"] == "Eric":
                    index_eric = i
                if house["Favorite Music"] == "hip hop":
                    index_hiphop = i
            if index_eric is None or index_hiphop is None or not (index_eric < index_hiphop) or abs(index_eric - index_hiphop) != 1:
                valid = False
            if not valid:
                continue
            
            # Constraint 3: Carol is in the sixth house.
            if houses[5]["Name"] != "Carol":
                valid = False
            if not valid:
                continue
            
            # Constraint 9: The person who loves hip-hop music is in the third house.
            if houses[2]["Favorite Music"] != "hip hop":
                valid = False
            if not valid:
                continue
            
            # If all constraints are met, record the solution.
            solutions.append(houses)
    
    # Use the first found solution (assuming unique solution)
    if solutions:
        sol = solutions[0]
        # Prepare the result as specified: header and rows (ordered by house number)
        result = {
            "solution": {
                "header": ["House", "Name", "Favorite Music"],
                "rows": [[house["House"], house["Name"], house["Favorite Music"]] for house in sol]
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == '__main__':
    main()