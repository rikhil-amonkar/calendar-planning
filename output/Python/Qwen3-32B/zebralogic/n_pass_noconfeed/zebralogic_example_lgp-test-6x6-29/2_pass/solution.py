def is_valid_solution(houses):
    # Check all constraints
    # 1. Alice is in the fifth house.
    if houses[4][1] != 'Alice':
        return False

    # 2. The person who loves stir fry is in a colonial-style house.
    try:
        stir_fry_house = next(i for i, h in enumerate(houses) if h[3] == 'stir fry')
    except StopIteration:
        return False  # If no 'stir fry' found
    if houses[stir_fry_house][1] == 'Alice':
        return False
    if houses[stir_fry_house][2] != 'colonial':
        return False

    # 3. Alice is the person who loves spaghetti.
    if houses[4][3] != 'spaghetti':
        return False

    # 4. Arnold is the person who loves stew.
    arnold_house = next(i for i, h in enumerate(houses) if h[1] == 'Arnold')
    if houses[arnold_house][3] != 'stew':
        return False

    # 5. One house between average height and Peter.
    avg_height_house = next(i for i, h in enumerate(houses) if h[5] == 'average')
    peter_house = next(i for i, h in enumerate(houses) if h[1] == 'Peter')
    if abs(avg_height_house - peter_house) != 2:
        return False

    # 6. Craftsman-style house is not in the third house.
    if houses[2][2] == 'craftsman':
        return False

    # 7. Average height is the stir fry lover.
    if houses[stir_fry_house][5] != 'average':
        return False

    # 8. Ranch-style house has beach vacation.
    ranch_house = next(i for i, h in enumerate(houses) if h[2] == 'ranch')
    if houses[ranch_house][4] != 'beach':
        return False

    # 9. Eric is in the fourth house.
    if houses[3][1] != 'Eric':
        return False

    # 10. Colonial and camping are one house apart.
    camping_house = next(i for i, h in enumerate(houses) if h[4] == 'camping')
    if abs(stir_fry_house - camping_house) != 1:
        return False

    # 11. Mountain lover smokes Yellow Monster.
    mountain_house = next(i for i, h in enumerate(houses) if h[4] == 'mountain')
    if houses[mountain_house][6] != 'yellow monster':
        return False

    # 12. Mountain lover is very tall.
    if houses[mountain_house][5] != 'very tall':
        return False

    # 13. Mountain lover and Dunhill smoker are next to each other.
    dunhill_house = next(i for i, h in enumerate(houses) if h[6] == 'dunhill')
    if abs(mountain_house - dunhill_house) != 1:
        return False

    # 14. Spaghetti lover resides in a Victorian house.
    if houses[4][2] != 'victorian':
        return False

    # 15. Tall person has beach vacation.
    tall_house = next(i for i, h in enumerate(houses) if h[5] == 'tall')
    if houses[tall_house][4] != 'beach':
        return False

    # 16. Tall is to the left of Victorian.
    if tall_house >= 4:
        return False

    # 17. Stir fry lover is directly left of Bob.
    bob_house = next(i for i, h in enumerate(houses) if h[1] == 'Bob')
    if stir_fry_house != bob_house - 1:
        return False

    # 18. Modern is to the left of Alice.
    modern_house = next(i for i, h in enumerate(houses) if h[2] == 'modern')
    if modern_house >= 4:
        return False

    # 19. Craftsman is to the left of short.
    craftsman_house = next(i for i, h in enumerate(houses) if h[2] == 'craftsman')
    short_house = next(i for i, h in enumerate(houses) if h[5] == 'short')
    if craftsman_house >= short_house:
        return False

    # 20. Stir fry is to the left of Prince.
    prince_house = next(i for i, h in enumerate(houses) if h[6] == 'prince')
    if stir_fry_house >= prince_house:
        return False

    # 21. Grilled cheese and super tall have two houses between.
    grilled_cheese_house = next(i for i, h in enumerate(houses) if h[3] == 'grilled cheese')
    super_tall_house = next(i for i, h in enumerate(houses) if h[5] == 'super tall')
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
    cultural_house = next(i for i, h in enumerate(houses) if h[4] == 'cultural')
    if houses[cultural_house][3] != 'pizza':
        return False

    # 25. Pizza lover is to the left of cruise.
    cruise_house = next(i for i, h in enumerate(houses) if h[4] == 'cruise')
    pizza_house = next(i for i, h in enumerate(houses) if h[3] == 'pizza')
    if pizza_house >= cruise_house:
        return False

    return True