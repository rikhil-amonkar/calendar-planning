import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    Cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    Mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    Hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Helper to create position dict from house->value mapping
    def invert(mapping):
        return {v: i for i, v in enumerate(mapping)}

    solution = None

    # Generate car assignments with constraints:
    # - Toyota Camry in house 6
    # - Ford F-150 in house 4 (deduced from clues 1, 5, 9)
    # - Chevy Silverado not in house 2
    # - Aniya (Chevy) is to the right of Honda -> Chevy house > Honda house (clue 11 + 3)
    remaining_cars = ['honda civic', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    # Houses available for remaining cars (1,2,3,5); 4 is Ford, 6 is Toyota
    car_house_slots = [1, 2, 3, 5]
    for perm in itertools.permutations(remaining_cars):
        car_at = [None] * 7  # index by house 1..6
        car_at[4] = 'ford f150'
        car_at[6] = 'toyota camry'
        ok = True
        for h, car in zip(car_house_slots, perm):
            car_at[h] = car
        if car_at[2] == 'chevrolet silverado':
            continue
        car_pos = invert(car_at)
        # Aniya right of Honda -> Chevy right of Honda
        if not (car_pos['chevrolet silverado'] > car_pos['honda civic']):
            continue

        # Mothers assignment:
        # Fixed:
        # - Sarah at 4
        # - Kailyn at 6
        # - Aniya at house of Chevy
        mother_at = [None] * 7
        mother_at[4] = 'Sarah'
        mother_at[6] = 'Kailyn'
        mother_at[car_pos['chevrolet silverado']] = 'Aniya'
        used_houses = {4, 6, car_pos['chevrolet silverado']}
        remaining_mothers = [m for m in Mothers if m not in ['Sarah', 'Kailyn', 'Aniya']]
        remaining_house_slots = [h for h in houses if h not in used_houses]
        for mperm in itertools.permutations(remaining_mothers):
            for h, m in zip(remaining_house_slots, mperm):
                mother_at[h] = m
            mother_pos = invert(mother_at)
            # Re-check clue 11 using mothers (redundant due to car check but safe):
            if not (mother_pos['Aniya'] > car_pos['honda civic']):
                continue

            # Names assignment:
            name_at = [None] * 7
            # - Bob at BMW
            name_at[car_pos['bmw 3 series']] = 'Bob'
            # - Arnold at Honda
            name_at[car_pos['honda civic']] = 'Arnold'
            # - Eric is directly left of knitting AND Holly is directly left of knitting
            #   -> The house directly left of knitting is both Eric and has mother Holly.
            #   So Eric is in the house whose mother is Holly.
            name_at[mother_pos['Holly']] = 'Eric'
            # - Alice somewhere to the right of Ford (house 4) -> Alice in 5 or 6
            possible_alice_houses = [h for h in [5, 6] if name_at[h] is None]
            if not possible_alice_houses:
                continue
            for alice_house in possible_alice_houses:
                name_at2 = name_at[:]
                name_at2[alice_house] = 'Alice'
                # Remaining names: Peter, Carol
                remaining_names = [n for n in Names if n not in name_at2[1:]]
                remaining_slots = [h for h in houses if name_at2[h] is None]
                for nperm in itertools.permutations(remaining_names):
                    name_at3 = name_at2[:]
                    ok_names = True
                    for h, n in zip(remaining_slots, nperm):
                        name_at3[h] = n
                    # Hobbies assignment:
                    # Constraints:
                    # - Eric is gardening
                    # - Carol is photography
                    # - Eric is directly left of knitting
                    # - Holly is directly left of knitting
                    # - Woodworking left of knitting
                    # - Penny right of knitting
                    # - Cooking is 2 houses away from Sarah (Sarah at 4) -> cooking at 2 or 6
                    hobby_at = [None] * 7
                    pos_eric = invert(name_at3)['Eric']
                    pos_carol = invert(name_at3)['Carol']
                    pos_holly = invert(mother_at)['Holly']
                    pos_penny = invert(mother_at)['Penny']
                    pos_sarah = invert(mother_at)['Sarah']  # should be 4

                    # Eric must be in the Holly house (derived); already enforced by names
                    if pos_eric != pos_holly:
                        continue

                    # Set gardening and knitting based on Eric
                    pos_knit = pos_eric + 1
                    if pos_knit > 6:
                        continue
                    # Penny somewhere to the right of knitting
                    if not (pos_penny > pos_knit):
                        continue

                    hobby_at[pos_eric] = 'gardening'
                    # If photography conflicts with gardening at Eric's house, it's already avoided as Carol != Eric
                    hobby_at[pos_knit] = 'knitting'
                    hobby_at[pos_carol] = 'photography'

                    # Cooking at 2 or 6 (one house between Sarah(4) and cooking)
                    for pos_cook in [2, 6]:
                        if hobby_at[pos_cook] is not None:
                            continue
                        hobby_at2 = hobby_at[:]
                        hobby_at2[pos_cook] = 'cooking'

                        # Woodworking must be somewhere to the left of knitting
                        remaining_hobby_slots = [h for h in houses if hobby_at2[h] is None]
                        remaining_hobbies = [h for h in Hobbies if h not in hobby_at2[1:]]
                        # Remaining should be two hobbies: woodworking and painting
                        if set(remaining_hobbies) != set(['woodworking', 'painting']):
                            continue
                        # Woodworking position options: any unfilled house < pos_knit
                        wood_options = [h for h in remaining_hobby_slots if h < pos_knit]
                        if not wood_options:
                            continue
                        for pos_wood in wood_options:
                            hobby_at3 = hobby_at2[:]
                            hobby_at3[pos_wood] = 'woodworking'
                            # Paint goes to the last unfilled
                            last_slot = [h for h in houses if hobby_at3[h] is None]
                            if len(last_slot) != 1:
                                continue
                            hobby_at3[last_slot[0]] = 'painting'

                            # Final validation of all clues:

                            # 1. Toyota Camry in 6
                            if car_at[6] != 'toyota camry':
                                continue
                            # 2. Carol is the photography enthusiast.
                            if hobby_at3[pos_carol] != 'photography':
                                continue
                            # 3. Chevy = Aniya
                            if mother_at[car_pos['chevrolet silverado']] != 'Aniya':
                                continue
                            # 4. Chevy not in 2
                            if car_at[2] == 'chevrolet silverado':
                                continue
                            # 5. Ford = Sarah
                            if mother_at[car_pos['ford f150']] != 'Sarah':
                                continue
                            # 6. BMW = Bob
                            if name_at3[car_pos['bmw 3 series']] != 'Bob':
                                continue
                            # 7. Kailyn in 6
                            if mother_at[6] != 'Kailyn':
                                continue
                            # 8. Eric directly left of knitting
                            if not (invert(name_at3)['Eric'] + 1 == invert(hobby_at3)['knitting']):
                                continue
                            # 9. One house between Sarah and Toyota
                            if abs(invert(mother_at)['Sarah'] - car_pos['toyota camry']) != 2:
                                continue
                            # 10. Penny to the right of knitting
                            if not (invert(mother_at)['Penny'] > invert(hobby_at3)['knitting']):
                                continue
                            # 11. Aniya to the right of Honda
                            if not (invert(mother_at)['Aniya'] > car_pos['honda civic']):
                                continue
                            # 12. Alice to the right of Ford (house 4)
                            if not (invert(name_at3)['Alice'] > car_pos['ford f150']):
                                continue
                            # 13. Eric is gardening
                            if hobby_at3[invert(name_at3)['Eric']] != 'gardening':
                                continue
                            # 14. Woodworking left of knitting
                            if not (invert(hobby_at3)['woodworking'] < invert(hobby_at3)['knitting']):
                                continue
                            # 15. One house between Sarah and cooking
                            if abs(invert(mother_at)['Sarah'] - invert(hobby_at3)['cooking']) != 2:
                                continue
                            # 16. Honda Civic is Arnold
                            if name_at3[car_pos['honda civic']] != 'Arnold':
                                continue
                            # 17. Holly directly left of knitting
                            if not (invert(mother_at)['Holly'] + 1 == invert(hobby_at3)['knitting']):
                                continue

                            # All constraints satisfied
                            final_rows = []
                            for h in houses:
                                final_rows.append([
                                    str(h),
                                    name_at3[h],
                                    car_at[h],
                                    mother_at[h],
                                    hobby_at3[h]
                                ])
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                                    "rows": final_rows
                                }
                            }
                            return solution

    return None

def main():
    sol = solve()
    if sol is None:
        print(json.dumps({"error": "No solution found"}))
    else:
        print(json.dumps(sol, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()