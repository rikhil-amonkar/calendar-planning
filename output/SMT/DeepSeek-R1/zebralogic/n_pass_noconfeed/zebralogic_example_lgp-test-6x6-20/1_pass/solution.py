import z3
import json

def main():
    # Create solver
    solver = z3.Solver()

    # Define the attributes and their values
    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

    # Create EnumSorts for each attribute
    NameSort, (Alice, Peter, Eric, Bob, Arnold, Carol) = z3.EnumSort('Name', names)
    CigarSort, (pall_mall, yellow_monster, dunhill, blue_master, prince, blends) = z3.EnumSort('Cigar', cigars)
    MusicSort, (hip_hop, jazz, country, pop, classical, rock) = z3.EnumSort('Music', music_genres)
    DrinkSort, (water, milk, boba_tea, tea, root_beer, coffee) = z3.EnumSort('Drink', drinks)
    MotherSort, (Kailyn, Penny, Janelle, Holly, Sarah, Aniya) = z3.EnumSort('Mother', mothers)
    FoodSort, (soup, pizza, spaghetti, stir_fry, stew, grilled_cheese) = z3.EnumSort('Food', foods)

    # Create variables for each house and attribute
    house_names = [z3.Const(f'name_{i}', NameSort) for i in range(1, 7)]
    house_cigars = [z3.Const(f'cigar_{i}', CigarSort) for i in range(1, 7)]
    house_music = [z3.Const(f'music_{i}', MusicSort) for i in range(1, 7)]
    house_drinks = [z3.Const(f'drink_{i}', DrinkSort) for i in range(1, 7)]
    house_mothers = [z3.Const(f'mother_{i}', MotherSort) for i in range(1, 7)]
    house_foods = [z3.Const(f'food_{i}', FoodSort) for i in range(1, 7)]

    # Add distinct constraints for each attribute
    solver.add(z3.Distinct(house_names))
    solver.add(z3.Distinct(house_cigars))
    solver.add(z3.Distinct(house_music))
    solver.add(z3.Distinct(house_drinks))
    solver.add(z3.Distinct(house_mothers))
    solver.add(z3.Distinct(house_foods))

    # Helper function to get house number for a value in an attribute list
    def get_house(attr_list, value):
        house = z3.Int(f'house_{value}')
        solver.add(house >= 1, house <= 6)
        for idx in range(6):
            solver.add(z3.If(attr_list[idx] == value, house == idx+1, True))
        return house

    # Create house variables for non-adjacent constraints
    carol_house = get_house(house_names, Carol)
    holly_house = get_house(house_mothers, Holly)
    grilled_cheese_house = get_house(house_foods, grilled_cheese)
    rock_house = get_house(house_music, rock)
    sarah_house = get_house(house_mothers, Sarah)
    yellow_monster_house = get_house(house_cigars, yellow_monster)
    pall_mall_house = get_house(house_cigars, pall_mall)
    stir_fry_house = get_house(house_foods, stir_fry)
    arnold_house = get_house(house_names, Arnold)
    kailyn_house = get_house(house_mothers, Kailyn)
    spaghetti_house = get_house(house_foods, spaghetti)
    blends_house = get_house(house_cigars, blends)

    # Add constraints from clues
    # 1. Carol is directly left of grilled cheese eater
    for i in range(5):
        solver.add(z3.Implies(house_names[i] == Carol, house_foods[i+1] == grilled_cheese))

    # 2. Eric is not in second house
    solver.add(house_names[1] != Eric)

    # 3. Holly is right of Carol
    solver.add(holly_house > carol_house)

    # 4. Grilled cheese is right of rock music
    solver.add(grilled_cheese_house > rock_house)

    # 5. Eric is directly left of Carol
    for i in range(5):
        solver.add(z3.Implies(house_names[i] == Eric, house_names[i+1] == Carol))

    # 6. Pop music not in third house
    solver.add(house_music[2] != pop)

    # 7. Eric loves country music
    for i in range(6):
        solver.add(z3.If(house_names[i] == Eric, house_music[i] == country, True))

    # 8. Classical music in sixth house
    solver.add(house_music[5] == classical)

    # 9. Coffee drinker is Bob
    for i in range(6):
        solver.add(z3.If(house_drinks[i] == coffee, house_names[i] == Bob, True))

    # 10. Blends smoker is Peter
    for i in range(6):
        solver.add(z3.If(house_cigars[i] == blends, house_names[i] == Peter, True))

    # 11. Stew not in fifth house
    solver.add(house_foods[4] != stew)

    # 12. Root beer directly left of Janelle
    for i in range(5):
        solver.add(z3.Implies(house_drinks[i] == root_beer, house_mothers[i+1] == Janelle))

    # 13. Two houses between Sarah and Yellow Monster
    solver.add(z3.Or(
        sarah_house - yellow_monster_house == 3,
        yellow_monster_house - sarah_house == 3
    ))

    # 14. Eric is tea drinker
    for i in range(6):
        solver.add(z3.If(house_names[i] == Eric, house_drinks[i] == tea, True))

    # 15. Pall Mall right of stir fry
    solver.add(pall_mall_house > stir_fry_house)

    # 16. Soup eater is Bob
    for i in range(6):
        solver.add(z3.If(house_foods[i] == soup, house_names[i] == Bob, True))

    # 17. Hip hop directly left of Kailyn
    for i in range(5):
        solver.add(z3.Implies(house_music[i] == hip_hop, house_mothers[i+1] == Kailyn))

    # 18. Arnold right of Kailyn
    solver.add(arnold_house > kailyn_house)

    # 19. Water directly left of Blue Master
    for i in range(5):
        solver.add(z3.Implies(house_drinks[i] == water, house_cigars[i+1] == blue_master))

    # 20. Spaghetti left of blends
    solver.add(spaghetti_house < blends_house)

    # 21. Sarah directly left of jazz
    for i in range(5):
        solver.add(z3.Implies(house_mothers[i] == Sarah, house_music[i+1] == jazz))

    # 22. Hip hop directly left of root beer
    for i in range(5):
        solver.add(z3.Implies(house_music[i] == hip_hop, house_drinks[i+1] == root_beer))

    # 23. Water drinker is stew eater
    for i in range(6):
        solver.add(z3.If(house_drinks[i] == water, house_foods[i] == stew, True))

    # 24. Dunhill not in second house
    solver.add(house_cigars[1] != dunhill)

    # 25. Milk drinker is Janelle
    for i in range(6):
        solver.add(z3.If(house_drinks[i] == milk, house_mothers[i] == Janelle, True))

    # 26. Eric is Aniya
    for i in range(6):
        solver.add(z3.If(house_names[i] == Eric, house_mothers[i] == Aniya, True))

    # Check if solver is satisfied
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Map house indices to attribute values
        solution_rows = []
        for i in range(6):
            name_val = model.eval(house_names[i])
            cigar_val = model.eval(house_cigars[i])
            music_val = model.eval(house_music[i])
            drink_val = model.eval(house_drinks[i])
            mother_val = model.eval(house_mothers[i])
            food_val = model.eval(house_foods[i])
            
            # Convert Z3 symbols to strings
            row = [
                str(i+1),
                str(name_val),
                str(cigar_val),
                str(music_val),
                str(drink_val),
                str(mother_val),
                str(food_val)
            ]
            solution_rows.append(row)
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()