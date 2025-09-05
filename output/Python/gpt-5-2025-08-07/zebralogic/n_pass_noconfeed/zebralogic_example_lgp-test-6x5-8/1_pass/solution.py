import json
from copy import deepcopy

def solve_puzzle():
    houses = [{"Name": None, "Animal": None, "Occupation": None, "FavoriteSport": None, "Height": None} for _ in range(6)]

    names = ['Arnold','Peter','Bob','Eric','Carol','Alice']
    animals = ['horse','rabbit','fish','cat','bird','dog']
    occupations = ['engineer','nurse','lawyer','teacher','artist','doctor']
    sports = ['basketball','volleyball','soccer','tennis','baseball','swimming']
    heights = ['average','tall','short','very short','very tall','super tall']

    # Remaining value sets for uniqueness
    remaining = {
        "Name": set(names),
        "Animal": set(animals),
        "Occupation": set(occupations),
        "FavoriteSport": set(sports),
        "Height": set(heights)
    }

    # Apply fixed clues directly
    # 18. The person who loves baseball is in the first house.
    houses[0]['FavoriteSport'] = 'baseball'
    remaining["FavoriteSport"].remove('baseball')

    # 9. The person who is a lawyer is in the fifth house.
    houses[4]['Occupation'] = 'lawyer'
    remaining["Occupation"].remove('lawyer')

    # 20. The person who is super tall is in the fifth house.
    houses[4]['Height'] = 'super tall'
    remaining["Height"].remove('super tall')

    # Helper to find position of a value in a category
    def get_pos(category, value):
        for i in range(6):
            if houses[i][category] == value:
                return i
        return None

    def any_house(indices, category, allowed_values):
        for i in indices:
            if houses[i][category] in allowed_values:
                return True
        return False

    def check_constraints():
        # 1. engineer = dog
        pos_engineer = get_pos('Occupation', 'engineer')
        pos_dog = get_pos('Animal', 'dog')
        if pos_engineer is not None and pos_dog is not None and pos_engineer != pos_dog:
            return False
        if pos_engineer is not None:
            if houses[pos_engineer]['Animal'] not in (None, 'dog'):
                return False
        if pos_dog is not None:
            if houses[pos_dog]['Occupation'] not in (None, 'engineer'):
                return False

        # 2. average left of short
        pos_avg = get_pos('Height', 'average')
        pos_short = get_pos('Height', 'short')
        if pos_avg is not None and pos_short is not None:
            if not (pos_avg < pos_short):
                return False
        elif pos_avg is not None and pos_short is None:
            # ensure possibility to the right
            if not any(i > pos_avg and houses[i]['Height'] in (None, 'short') for i in range(6)):
                return False
        elif pos_short is not None and pos_avg is None:
            if not any(i < pos_short and houses[i]['Height'] in (None, 'average') for i in range(6)):
                return False

        # 3. average directly left of rabbit
        pos_rabbit = get_pos('Animal', 'rabbit')
        if pos_avg is not None and pos_rabbit is not None:
            if pos_rabbit != pos_avg + 1:
                return False
        if pos_avg is not None:
            if pos_avg == 5:
                return False
            right = pos_avg + 1
            if houses[right]['Animal'] not in (None, 'rabbit'):
                return False
        if pos_rabbit is not None:
            if pos_rabbit == 0:
                return False
            left = pos_rabbit - 1
            if houses[left]['Height'] not in (None, 'average'):
                return False

        # 4. tall left of very short
        pos_tall = get_pos('Height', 'tall')
        pos_very_short = get_pos('Height', 'very short')
        if pos_tall is not None and pos_very_short is not None:
            if not (pos_tall < pos_very_short):
                return False
        elif pos_tall is not None and pos_very_short is None:
            if not any(i > pos_tall and houses[i]['Height'] in (None, 'very short') for i in range(6)):
                return False
        elif pos_very_short is not None and pos_tall is None:
            if not any(i < pos_very_short and houses[i]['Height'] in (None, 'tall') for i in range(6)):
                return False

        # 5. Arnold = cat
        pos_arnold = get_pos('Name', 'Arnold')
        pos_cat = get_pos('Animal', 'cat')
        if pos_arnold is not None and pos_cat is not None and pos_arnold != pos_cat:
            return False
        if pos_arnold is not None:
            if houses[pos_arnold]['Animal'] not in (None, 'cat'):
                return False
        if pos_cat is not None:
            if houses[pos_cat]['Name'] not in (None, 'Arnold'):
                return False

        # 6. horses = teacher
        pos_teacher = get_pos('Occupation', 'teacher')
        pos_horse = get_pos('Animal', 'horse')
        if pos_teacher is not None and pos_horse is not None and pos_teacher != pos_horse:
            return False
        if pos_teacher is not None:
            if houses[pos_teacher]['Animal'] not in (None, 'horse'):
                return False
        if pos_horse is not None:
            if houses[pos_horse]['Occupation'] not in (None, 'teacher'):
                return False

        # 7. Carol = soccer
        pos_carol = get_pos('Name', 'Carol')
        pos_soccer = get_pos('FavoriteSport', 'soccer')
        if pos_carol is not None and pos_soccer is not None and pos_carol != pos_soccer:
            return False
        if pos_carol is not None:
            if houses[pos_carol]['FavoriteSport'] not in (None, 'soccer'):
                return False
        if pos_soccer is not None:
            if houses[pos_soccer]['Name'] not in (None, 'Carol'):
                return False

        # 8. tall = volleyball
        pos_volleyball = get_pos('FavoriteSport', 'volleyball')
        if pos_tall is not None and pos_volleyball is not None and pos_tall != pos_volleyball:
            return False
        if pos_tall is not None:
            if houses[pos_tall]['FavoriteSport'] not in (None, 'volleyball'):
                return False
        if pos_volleyball is not None:
            if houses[pos_volleyball]['Height'] not in (None, 'tall'):
                return False

        # 9. lawyer in 5th house (already set), enforce consistency
        if houses[4]['Occupation'] not in (None, 'lawyer'):
            return False
        # also ensure no other house is assigned lawyer
        for i in range(6):
            if i != 4 and houses[i]['Occupation'] == 'lawyer':
                return False

        # 10. tennis = teacher
        pos_tennis = get_pos('FavoriteSport', 'tennis')
        if pos_teacher is not None and pos_tennis is not None and pos_teacher != pos_tennis:
            return False
        if pos_teacher is not None:
            if houses[pos_teacher]['FavoriteSport'] not in (None, 'tennis'):
                return False
        if pos_tennis is not None:
            if houses[pos_tennis]['Occupation'] not in (None, 'teacher'):
                return False

        # 11. average = swimming
        pos_swimming = get_pos('FavoriteSport', 'swimming')
        if pos_avg is not None and pos_swimming is not None and pos_avg != pos_swimming:
            return False
        if pos_avg is not None:
            if houses[pos_avg]['FavoriteSport'] not in (None, 'swimming'):
                return False
        if pos_swimming is not None:
            if houses[pos_swimming]['Height'] not in (None, 'average'):
                return False

        # 12. baseball directly left of engineer
        pos_baseball = get_pos('FavoriteSport', 'baseball')
        pos_engineer = get_pos('Occupation', 'engineer')
        if pos_baseball is not None and pos_engineer is not None:
            if pos_engineer != pos_baseball + 1:
                return False
        if pos_baseball is not None:
            if pos_baseball == 5:
                return False
            right = pos_baseball + 1
            if houses[right]['Occupation'] not in (None, 'engineer'):
                return False
        if pos_engineer is not None:
            if pos_engineer == 0:
                return False
            left = pos_engineer - 1
            if houses[left]['FavoriteSport'] not in (None, 'baseball'):
                return False

        # 13. Peter = nurse
        pos_peter = get_pos('Name', 'Peter')
        pos_nurse = get_pos('Occupation', 'nurse')
        if pos_peter is not None and pos_nurse is not None and pos_peter != pos_nurse:
            return False
        if pos_peter is not None:
            if houses[pos_peter]['Occupation'] not in (None, 'nurse'):
                return False
        if pos_nurse is not None:
            if houses[pos_nurse]['Name'] not in (None, 'Peter'):
                return False

        # 14. Bob right of artist
        pos_bob = get_pos('Name', 'Bob')
        pos_artist = get_pos('Occupation', 'artist')
        if pos_bob is not None and pos_artist is not None:
            if not (pos_bob > pos_artist):
                return False
        if pos_bob is not None and pos_artist is None:
            if not any(i < pos_bob and houses[i]['Occupation'] in (None, 'artist') for i in range(6)):
                return False
        if pos_artist is not None and pos_bob is None:
            if not any(i > pos_artist and houses[i]['Name'] in (None, 'Bob') for i in range(6)):
                return False

        # 15. teacher directly left of soccer
        if pos_teacher is not None and pos_soccer is not None:
            if pos_soccer != pos_teacher + 1:
                return False
        if pos_teacher is not None:
            if pos_teacher == 5:
                return False
            right = pos_teacher + 1
            if houses[right]['FavoriteSport'] not in (None, 'soccer'):
                return False
        if pos_soccer is not None:
            if pos_soccer == 0:
                return False
            left = pos_soccer - 1
            if houses[left]['Occupation'] not in (None, 'teacher'):
                return False

        # 16. rabbit = Alice
        pos_alice = get_pos('Name', 'Alice')
        if pos_rabbit is not None and pos_alice is not None and pos_rabbit != pos_alice:
            return False
        if pos_rabbit is not None:
            if houses[pos_rabbit]['Name'] not in (None, 'Alice'):
                return False
        if pos_alice is not None:
            if houses[pos_alice]['Animal'] not in (None, 'rabbit'):
                return False

        # 17. fish = Carol
        pos_fish = get_pos('Animal', 'fish')
        if pos_carol is not None and pos_fish is not None and pos_carol != pos_fish:
            return False
        if pos_carol is not None:
            if houses[pos_carol]['Animal'] not in (None, 'fish'):
                return False
        if pos_fish is not None:
            if houses[pos_fish]['Name'] not in (None, 'Carol'):
                return False

        # 18. baseball in first house (already set), enforce consistency:
        if houses[0]['FavoriteSport'] not in (None, 'baseball'):
            return False
        for i in range(1,6):
            if houses[i]['FavoriteSport'] == 'baseball':
                return False

        # 19. cat right of very short
        if pos_cat is not None and pos_very_short is not None:
            if not (pos_cat > pos_very_short):
                return False
        if pos_cat is not None and pos_very_short is None:
            if not any(i < pos_cat and houses[i]['Height'] in (None, 'very short') for i in range(6)):
                return False
        if pos_very_short is not None and pos_cat is None:
            if not any(i > pos_very_short and houses[i]['Animal'] in (None, 'cat') for i in range(6)):
                return False

        # 20. super tall in fifth house (already set), enforce consistency:
        if houses[4]['Height'] not in (None, 'super tall'):
            return False
        for i in range(6):
            if i != 4 and houses[i]['Height'] == 'super tall':
                return False

        # Also ensure uniqueness so far within each category: no duplicate assignments across houses
        for category in ["Name", "Animal", "Occupation", "FavoriteSport", "Height"]:
            seen = set()
            for i in range(6):
                v = houses[i][category]
                if v is not None:
                    if v in seen:
                        return False
                    seen.add(v)

        return True

    def assign_house(idx):
        # Move to next unassigned house index
        while idx < 6:
            # Check if all attributes of this house are assigned
            complete = True
            for cat in ["Name", "Animal", "Occupation", "FavoriteSport", "Height"]:
                if houses[idx][cat] is None:
                    complete = False
                    break
            if complete:
                idx += 1
            else:
                break

        if idx == 6:
            # All houses assigned
            return check_constraints()

        # Determine order of attributes to assign for this house
        cats_order = ["Name", "Animal", "Occupation", "FavoriteSport", "Height"]
        # For current house, build candidate lists per category
        candidates = {}
        for cat in cats_order:
            if houses[idx][cat] is not None:
                candidates[cat] = [houses[idx][cat]]
            else:
                candidates[cat] = list(remaining[cat])

        # Simple heuristic: sort categories by smallest domain to reduce branching
        cats_order_sorted = sorted(cats_order, key=lambda c: len(candidates[c]))

        def backtrack_attrs(cat_index):
            if cat_index == len(cats_order_sorted):
                # After assigning all attributes for this house, check constraints and recurse
                if not check_constraints():
                    return False
                return assign_house(idx + 1)

            cat = cats_order_sorted[cat_index]
            if houses[idx][cat] is not None:
                # Already assigned
                return backtrack_attrs(cat_index + 1)

            for val in list(candidates[cat]):
                # Try assign val to this house in this category
                if val not in remaining[cat]:
                    continue
                houses[idx][cat] = val
                remaining[cat].remove(val)

                # Early check
                if check_constraints():
                    if backtrack_attrs(cat_index + 1):
                        return True

                # Undo
                remaining[cat].add(val)
                houses[idx][cat] = None

            return False

        return backtrack_attrs(0)

    success = assign_house(0)
    if not success:
        raise RuntimeError("No solution found")

    # Build JSON output
    header = ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"]
    rows = []
    for i in range(6):
        row = [
            str(i + 1),
            houses[i]["Name"],
            houses[i]["Animal"],
            houses[i]["Occupation"],
            houses[i]["FavoriteSport"],
            houses[i]["Height"],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))