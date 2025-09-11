import json
import itertools

# Define all possible values for each attribute
names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
house_styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
food = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
vacation = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
height = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
cigar = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

def is_valid_solution(houses):
    # Check all constraints
    # 1. Alice is in the fifth house.
    if houses[4][1] != 'Alice':
        return False
    # 2. The person who loves stir fry is in a colonial-style house.
    stir_fry_house = next(i for i, h in enumerate(houses) if h[2] == 'stir fry')
    if houses[stir_fry_house][2] != 'stir fry' or houses[stir_fry_house][1] == 'Alice':
        return False
    if houses[stir_fry_house][2] == 'stir fry' and houses[stir_fry_house][1] != 'Alice' and houses[stir_fry_house][3] != 'colonial':
        return False
    # 3. Alice is the person who loves spaghetti.
    if houses[4][2] != 'spaghetti':
        return False
    # 4. Arnold is the person who loves stew.
    arnold_house = next(i for i, h in enumerate(houses) if h[1] == 'Arnold')
    if houses[arnold_house][2] != 'stew':
        return False
    # 5. One house between average height and Peter.
    avg_height_house = next(i for i, h in enumerate(houses) if h[4] == 'average')
    peter_house = next(i for i, h in enumerate(houses) if h[1] == 'Peter')
    if abs(avg_height_house - peter_house) != 2:
        return False
    # 6. Craftsman-style house is not in the third house.
    if houses[2][3] == 'craftsman':
        return False
    # 7. Average height is the stir fry lover.
    if houses[stir_fry_house][4] != 'average':
        return False
    # 8. Ranch-style house has beach vacation.
    ranch_house = next(i for i, h in enumerate(houses) if h[3] == 'ranch')
    if houses[ranch_house][5] != 'beach':
        return False
    # 9. Eric is in the fourth house.
    if houses[3][1] != 'Eric':
        return False
    # 10. Colonial and camping are one house apart.
    camping_house = next(i for i, h in enumerate(houses) if h[5] == 'camping')
    if abs(stir_fry_house - camping_house) != 1:
        return False
    # 11. Mountain lover smokes Yellow Monster.
    mountain_house = next(i for i, h in enumerate(houses) if h[5] == 'mountain')
    if houses[mountain_house][6] != 'yellow monster':
        return False
    # 12. Mountain lover is very tall.
    if houses[mountain_house][4] != 'very tall':
        return False
    # 13. Mountain lover and Dunhill smoker are next to each other.
    dunhill_house = next(i for i, h in enumerate(houses) if h[6] == 'dunhill')
    if abs(mountain_house - dunhill_house) != 1:
        return False
    # 14. Spaghetti lover resides in a Victorian house.
    if houses[4][3] != 'victorian':
        return False
    # 15. Tall person has beach vacation.
    tall_house = next(i for i, h in enumerate(houses) if h[4] == 'tall')
    if houses[tall_house][5] != 'beach':
        return False
    # 16. Tall is to the left of Victorian.
    if tall_house >= 4:
        return False
    # 17. Stir fry lover is directly left of Bob.
    bob_house = next(i for i, h in enumerate(houses) if h[1] == 'Bob')
    if stir_fry_house != bob_house - 1:
        return False
    # 18. Modern is to the left of Alice.
    modern_house = next(i for i, h in enumerate(houses) if h[3] == 'modern')
    if modern_house >= 4:
        return False
    # 19. Craftsman is to the left of short.
    craftsman_house = next(i for i, h in enumerate(houses) if h[3] == 'craftsman')
    short_house = next(i for i, h in enumerate(houses) if h[4] == 'short')
    if craftsman_house >= short_house:
        return False
    # 20. Stir fry is to the left of Prince.
    prince_house = next(i for i, h in enumerate(houses) if h[6] == 'prince')
    if stir_fry_house >= prince_house:
        return False
    # 21. Grilled cheese and super tall have two houses between.
    grilled_cheese_house = next(i for i, h in enumerate(houses) if h[2] == 'grilled cheese')
    super_tall_house = next(i for i, h in enumerate(houses) if h[4] == 'super tall')
    if abs(grilled_cheese_house - super_tall_house) != 3:
        return False
    # 22. Ranch-style smokes Blue Master.
    if houses[ranch_house][6] != 'blue master':
        return False
    # 23. Blends is directly left of Blue Master.
    blends_house = next(i for i, h in enumerate(houses) if h[6] == 'blends')
    blue_master_house = next(i for i, h in enumerate(houses) if h[6] == 'blue master')
    if blends_house != blue_master_house - 1:
        return False
    # 24. Cultural is pizza lover.
    cultural_house = next(i for i, h in enumerate(houses) if h[5] == 'cultural')
    if houses[cultural_house][2] != 'pizza':
        return False
    # 25. Pizza lover is to the left of cruise.
    cruise_house = next(i for i, h in enumerate(houses) if h[5] == 'cruise')
    pizza_house = next(i for i, h in enumerate(houses) if h[2] == 'pizza')
    if pizza_house >= cruise_house:
        return False
    return True

def solve():
    # Generate valid names permutations (Eric in house 4, Alice in house 5)
    valid_names = [p for p in itertools.permutations(names) if p[3] == 'Eric' and p[4] == 'Alice']
    
    # Generate valid house styles permutations (Victorian in house 5)
    valid_house_styles = [p for p in itertools.permutations(house_styles) if p[4] == 'victorian']
    
    # Generate valid food permutations (Spaghetti in house 5)
    valid_food = [p for p in itertools.permutations(food) if p[4] == 'spaghetti']
    
    # Iterate through all possible combinations
    for names_p in valid_names:
        bob_house = names_p.index('Bob')
        peter_house = names_p.index('Peter')
        # Check if one house between average height and Peter (constraint 5)
        # We'll handle this during height permutation check
        for house_styles_p in valid_house_styles:
            # Check if colonial house is for stir fry (constraint 2)
            # We'll handle this during food permutation check
            for food_p in valid_food:
                # Find stir fry house
                stir_fry_house = food_p.index('stir fry')
                # Check if Bob is directly to the right (constraint 17)
                if stir_fry_house != bob_house - 1:
                    continue
                # Check if colonial house for stir fry (constraint 2)
                if house_styles_p[stir_fry_house] != 'colonial':
                    continue
                # Generate valid height permutations
                for height_p in itertools.permutations(height):
                    # Check if average height for stir fry (constraint 7)
                    if height_p[stir_fry_house] != 'average':
                        continue
                    # Check if one house between average height and Peter (constraint 5)
                    avg_height_house = height_p.index('average')
                    if abs(avg_height_house - peter_house) != 2:
                        continue
                    # Generate valid vacation permutations
                    for vacation_p in itertools.permutations(vacation):
                        # Check if camping is adjacent to colonial (constraint 10)
                        camping_house = vacation_p.index('camping')
                        if abs(stir_fry_house - camping_house) != 1:
                            continue
                        # Check if beach is in ranch-style (constraint 8)
                        ranch_house = house_styles_p.index('ranch')
                        if vacation_p[ranch_house] != 'beach':
                            continue
                        # Check if tall has beach (constraint 15)
                        tall_house = height_p.index('tall')
                        if vacation_p[tall_house] != 'beach':
                            continue
                        # Check if modern is left of Alice (constraint 18)
                        modern_house = house_styles_p.index('modern')
                        if modern_house >= 4:
                            continue
                        # Check if craftsman is left of short (constraint 19)
                        craftsman_house = house_styles_p.index('craftsman')
                        short_house = height_p.index('short')
                        if craftsman_house >= short_house:
                            continue
                        # Check if cultural is pizza (constraint 24)
                        cultural_house = vacation_p.index('cultural')
                        if food_p[cultural_house] != 'pizza':
                            continue
                        # Check if pizza is left of cruise (constraint 25)
                        cruise_house = vacation_p.index('cruise')
                        pizza_house = food_p.index('pizza')
                        if pizza_house >= cruise_house:
                            continue
                        # Generate valid cigar permutations
                        for cigar_p in itertools.permutations(cigar):
                            # Check if Blue Master in ranch (constraint 22)
                            if cigar_p[ranch_house] != 'blue master':
                                continue
                            # Check if blends is left of Blue Master (constraint 23)
                            blends_house = cigar_p.index('blends')
                            blue_master_house = cigar_p.index('blue master')
                            if blends_house != blue_master_house - 1:
                                continue
                            # Check if Yellow Monster in mountain (constraint 11)
                            mountain_house = vacation_p.index('mountain')
                            if cigar_p[mountain_house] != 'yellow monster':
                                continue
                            # Check if Dunhill is adjacent to mountain (constraint 13)
                            dunhill_house = cigar_p.index('dunhill')
                            if abs(mountain_house - dunhill_house) != 1:
                                continue
                            # Check if Prince is right of stir fry (constraint 20)
                            prince_house = cigar_p.index('prince')
                            if stir_fry_house >= prince_house:
                                continue
                            # Check if two houses between grilled cheese and super tall (constraint 21)
                            grilled_cheese_house = food_p.index('grilled cheese')
                            super_tall_house = height_p.index('super tall')
                            if abs(grilled_cheese_house - super_tall_house) != 3:
                                continue
                            # Build the solution
                            houses = []
                            for i in range(6):
                                house = [
                                    str(i + 1),
                                    names_p[i],
                                    house_styles_p[i],
                                    food_p[i],
                                    vacation_p[i],
                                    height_p[i],
                                    cigar_p[i]
                                ]
                                houses.append(house)
                            if is_valid_solution(houses):
                                return {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                        "rows": houses
                                    }
                                }
    return {"solution": {"header": [], "rows": []}}

solution = solve()
print(json.dumps(solution, indent=2))