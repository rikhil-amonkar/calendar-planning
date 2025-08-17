import itertools
import json

def solve():
    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']
    
    assignment = []
    used_names = set()
    used_cigars = set()
    used_music = set()
    used_drinks = set()
    used_mothers = set()
    used_foods = set()
    
    def check_partial_constraints(new_house, house_index):
        if house_index > 0:
            prev_house = assignment[house_index-1]
            # Check if previous house's name is Eric and current is not Carol
            if prev_house[0] == 'Eric' and new_house[0] != 'Carol':
                return False
            # Check if current house's name is Carol and previous is not Eric
            if new_house[0] == 'Carol' and prev_house[0] != 'Eric':
                return False
            # Check if current house is Eric and in second position (house_index == 1)
            if new_house[0] == 'Eric' and house_index == 1:
                return False
            # Check if previous house's drink is water and current cigar is blue master
            if prev_house[3] == 'water' and new_house[1] != 'blue master':
                return False
            # Check if previous house's music is hip hop and current mother is Kailyn
            if prev_house[2] == 'hip hop' and new_house[4] != 'Kailyn':
                return False
            # Check if previous house's music is hip hop and current drink is root beer
            if prev_house[2] == 'hip hop' and new_house[3] != 'root beer':
                return False
            # Check if previous house's drink is root beer and current mother is Janelle
            if prev_house[3] == 'root beer' and new_house[4] != 'Janelle':
                return False
            # Check if current house's cigar is Dunhill and house is 2 (index 1)
            if new_house[1] == 'dunhill' and house_index == 1:
                return False
            # Check if current house's food is stew and house is 5 (index 4)
            if new_house[5] == 'stew' and house_index == 4:
                return False
            # Check if current house's drink is water and food is stew
            if new_house[3] == 'water' and new_house[5] != 'stew':
                return False
            if new_house[5] == 'stew' and new_house[3] != 'water':
                return False
            # Check if current house's name is Bob and drink is coffee
            if new_house[0] == 'Bob' and new_house[3] != 'coffee':
                return False
            # Check if current house's name is Bob and food is soup
            if new_house[0] == 'Bob' and new_house[5] != 'soup':
                return False
            # Check if current house's name is Eric and drink is tea
            if new_house[0] == 'Eric' and new_house[3] != 'tea':
                return False
            # Check if current house's name is Eric and music is country
            if new_house[0] == 'Eric' and new_house[2] != 'country':
                return False
            # Check if current house's name is Eric and mother is Aniya
            if new_house[0] == 'Eric' and new_house[4] != 'Aniya':
                return False
            # Check if current house's mother is Janelle and drink is milk
            if new_house[4] == 'Janelle' and new_house[3] != 'milk':
                return False
            # Check if current house's music is classical and house is 6 (index 5)
            if new_house[2] == 'classical' and house_index != 5:
                return False
            # Check if current house's music is pop and house is 3 (index 2)
            if new_house[2] == 'pop' and house_index == 2:
                return False
            # Check if current house's name is Peter and cigar is blends
            if new_house[0] == 'Peter' and new_house[1] != 'blends':
                return False
            # Check if current house's food is grilled cheese, there is a rock music in previous houses
            if new_house[5] == 'grilled cheese':
                has_rock = any(h[2] == 'rock' for h in assignment)
                if not has_rock:
                    return False
            # Check if current house's cigar is Pall Mall and there is a stir fry in previous houses
            if new_house[1] == 'pall mall':
                has_stir_fry = any(h[5] == 'stir fry' for h in assignment)
                if not has_stir_fry:
                    return False
        else:
            # For the first house, check if music is classical (must be house 6)
            if new_house[2] == 'classical':
                return False
            # Check if first house's name is Carol (since Eric must be directly left of Carol, and Eric can't be in house 0)
            if new_house[0] == 'Carol':
                return False
        return True
    
    def all_constraints_satisfied(assignment):
        # Check clue 1: Carol directly left of grilled cheese
        for i in range(5):
            if assignment[i][0] == 'Carol' and assignment[i+1][5] != 'grilled cheese':
                return False
        # Check clue 3: Holly's mother is to the right of Carol
        carol_house = None
        holly_house = None
        for i, h in enumerate(assignment):
            if h[0] == 'Carol':
                carol_house = i
            if h[4] == 'Holly':
                holly_house = i
        if holly_house is not None and carol_house is not None and holly_house <= carol_house:
            return False
        # Check clue 4: grilled cheese is to the right of rock
        rock_house = None
        grilled_house = None
        for i, h in enumerate(assignment):
            if h[2] == 'rock':
                rock_house = i
            if h[5] == 'grilled cheese':
                grilled_house = i
        if rock_house is not None and grilled_house is not None and grilled_house <= rock_house:
            return False
        # Check clue 13: two houses between Sarah and Yellow Monster
        sarah_house = None
        yellow_house = None
        for i, h in enumerate(assignment):
            if h[4] == 'Sarah':
                sarah_house = i
            if h[1] == 'yellow monster':
                yellow_house = i
        if sarah_house is not None and yellow_house is not None:
            if abs(sarah_house - yellow_house) != 3:
                return False
        # Check clue 15: Pall Mall is to the right of stir fry
        stir_fry_house = None
        pall_mall_house = None
        for i, h in enumerate(assignment):
            if h[5] == 'stir fry':
                stir_fry_house = i
            if h[1] == 'pall mall':
                pall_mall_house = i
        if stir_fry_house is not None and pall_mall_house is not None and pall_mall_house <= stir_fry_house:
            return False
        # Check clue 20: spaghetti is left of blends (Peter)
        spaghetti_house = None
        blends_house = None
        for i, h in enumerate(assignment):
            if h[5] == 'spaghetti':
                spaghetti_house = i
            if h[1] == 'blends':  # Peter's cigar
                blends_house = i
        if spaghetti_house is not None and blends_house is not None and blends_house <= spaghetti_house:
            return False
        # Check clue 18: Arnold is to the right of Kailyn's mother
        kailyn_house = None
        arnold_house = None
        for i, h in enumerate(assignment):
            if h[4] == 'Kailyn':
                kailyn_house = i
            if h[0] == 'Arnold':
                arnold_house = i
        if kailyn_house is not None and arnold_house is not None and arnold_house <= kailyn_house:
            return False
        return True
    
    def backtrack(house_index):
        if house_index == 6:
            return assignment if all_constraints_satisfied(assignment) else None
        available_names = [n for n in names if n not in used_names]
        available_cigars = [c for c in cigars if c not in used_cigars]
        available_music = [m for m in music_genres if m not in used_music]
        available_drinks = [d for d in drinks if d not in used_drinks]
        available_mothers = [mo for mo in mothers if mo not in used_mothers]
        available_foods = [f for f in foods if f not in used_foods]
        
        for attrs in itertools.product(available_names, available_cigars, available_music, available_drinks, available_mothers, available_foods):
            name, cigar, music, drink, mother, food = attrs
            new_house = [name, cigar, music, drink, mother, food]
            if check_partial_constraints(new_house, house_index):
                assignment.append(new_house)
                used_names.add(name)
                used_cigars.add(cigar)
                used_music.add(music)
                used_drinks.add(drink)
                used_mothers.add(mother)
                used_foods.add(food)
                
                result = backtrack(house_index + 1)
                if result is not None:
                    return result
                
                assignment.pop()
                used_names.remove(name)
                used_cigars.remove(cigar)
                used_music.remove(music)
                used_drinks.remove(drink)
                used_mothers.remove(mother)
                used_foods.remove(food)
        return None
    
    solution = backtrack(0)
    if solution:
        # Format the solution as required
        header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
        rows = []
        for i, house in enumerate(solution, 1):
            rows.append([str(i)] + house)
        return {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
    else:
        return {"solution": None}

# Generate the JSON output
result = solve()
print(json.dumps(result, indent=2))