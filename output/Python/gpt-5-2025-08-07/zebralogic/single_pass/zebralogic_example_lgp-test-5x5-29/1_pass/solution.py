import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    Nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    Vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    Educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    Occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

    solutions = []

    # Iterate over all possible placements of names with early pruning from clues
    for name_positions in itertools.permutations(houses):
        pos_name = dict(zip(Names, name_positions))

        # Clue-derived quick prunes
        if pos_name['Peter'] == 1:  # Clue 5
            continue
        if pos_name['Bob'] == 4:    # Clue 13
            continue
        # Clue 2 implies Arnold cannot be 1
        if pos_name['Arnold'] == 1:
            continue
        # From mountain=5 and camping=Eric, Eric cannot be 5; from bachelor=3 and master=Eric, Eric cannot be 3
        if pos_name['Eric'] in (3, 5):
            continue

        # Vacations assignment with constraints (Clues 2,16,17,18,14,10,7)
        # Fixed: mountain=5, camping=Eric, beach = left of Arnold
        vac_pos = {}
        vac_pos['mountain'] = 5
        vac_pos['camping'] = pos_name['Eric']
        beach_pos = pos_name['Arnold'] - 1
        if beach_pos < 1 or beach_pos > 4:
            continue
        if beach_pos in (vac_pos['mountain'], vac_pos['camping']):
            continue
        vac_pos['beach'] = beach_pos

        # City must be to the right of beach and not in 5 (since 5 is mountain)
        used = {vac_pos['mountain'], vac_pos['camping'], vac_pos['beach']}
        candidate_cities = [h for h in houses if h not in used and h > vac_pos['beach'] and h != 5]
        if not candidate_cities:
            continue

        for city_pos in candidate_cities:
            vac_pos_local = vac_pos.copy()
            vac_pos_local['city'] = city_pos
            # Cruise is the remaining house; must be to the right of beach and not 5
            remaining = [h for h in houses if h not in set(vac_pos_local.values())]
            if len(remaining) != 1:
                continue
            cruise_pos = remaining[0]
            if cruise_pos <= vac_pos_local['beach'] or cruise_pos == 5:
                continue
            vac_pos_local['cruise'] = cruise_pos

            # Education assignment (Clues 19,7,4,3,9)
            ed_pos = {}
            ed_pos['bachelor'] = 3
            # master at Eric's house (camping=Eric)
            ed_pos['master'] = pos_name['Eric']
            # associate equals cruise
            ed_pos['associate'] = vac_pos_local['cruise']
            # Ensure no duplicate education positions among assigned
            if len({ed_pos['bachelor'], ed_pos['master'], ed_pos['associate']}) < 3:
                # e.g., would fail if associate=3 conflicting with bachelor=3
                continue
            # Remaining two: doctorate and high school
            remaining_ed_houses = [h for h in houses if h not in set(ed_pos.values())]
            # Try both ways for doctorate/high school
            for doc_pos in remaining_ed_houses:
                if not (doc_pos < pos_name['Bob']):  # Clue 3
                    continue
                ed_pos_local = ed_pos.copy()
                ed_pos_local['doctorate'] = doc_pos
                other = [h for h in remaining_ed_houses if h != doc_pos][0]
                ed_pos_local['high school'] = other

                # Occupations (Clues 6,12,1,4,9,8)
                occ_pos = {}
                # artist is Peter
                occ_pos['artist'] = pos_name['Peter']
                # lawyer equals cruise (and associate)
                occ_pos['lawyer'] = vac_pos_local['cruise']
                # engineer is immediately to the right of associate
                eng_pos = ed_pos_local['associate'] + 1
                if eng_pos < 1 or eng_pos > 5:
                    continue
                occ_pos['engineer'] = eng_pos
                # Check unique so far
                if len(set(occ_pos.values())) < 3:
                    continue
                # Remaining occupations: doctor, teacher
                remaining_occ_houses = [h for h in houses if h not in set(occ_pos.values())]
                if len(remaining_occ_houses) != 2:
                    continue
                # Two permutations for assigning doctor and teacher
                for doctor_house, teacher_house in [(remaining_occ_houses[0], remaining_occ_houses[1]),
                                                    (remaining_occ_houses[1], remaining_occ_houses[0])]:
                    occ_pos_local = occ_pos.copy()
                    occ_pos_local['doctor'] = doctor_house
                    occ_pos_local['teacher'] = teacher_house

                    # Nationalities (Clues 10,14,7 -> Eric is Brit; 12 -> Peter Swede; 15 -> Alice German; 11 adjacency; 8 Dane right of doctor)
                    nat_pos = {}
                    nat_pos['brit'] = pos_name['Eric']
                    nat_pos['swede'] = pos_name['Peter']
                    nat_pos['german'] = pos_name['Alice']
                    remaining_nat_houses = [h for h in houses if h not in set(nat_pos.values())]
                    # Remaining nationalities: norwegian and dane must fill remaining houses
                    # Norwegian must be adjacent to bachelor (house 3) -> house 2 or 4
                    possible_norwegian_houses = set(remaining_nat_houses).intersection({2, 4})
                    if not possible_norwegian_houses:
                        continue
                    # Try each possible placement for Norwegian; Dane gets the other remaining house
                    success_nat = False
                    for nor_house in possible_norwegian_houses:
                        nat_pos_local = nat_pos.copy()
                        nat_pos_local['norwegian'] = nor_house
                        dane_house = [h for h in remaining_nat_houses if h != nor_house][0]
                        nat_pos_local['dane'] = dane_house
                        # Check doctor < dane (Clue 8)
                        if not (occ_pos_local['doctor'] < nat_pos_local['dane']):
                            continue
                        # All constraints satisfied if we reach here
                        # Also ensure city is to the right of beach (already), cruise to the right (already), beach left of Arnold (already)
                        # Record solution
                        # Build per-house summary
                        house_info = {h: {} for h in houses}
                        for n in Names:
                            house_info[pos_name[n]]['Name'] = n
                        for nat in Nationalities:
                            house_info[nat_pos_local[nat]]['Nationality'] = nat
                        for vac in Vacations:
                            house_info[vac_pos_local[vac]]['Vacation'] = vac
                        for edu in Educations:
                            house_info[ed_pos_local[edu]]['Education'] = edu
                        for occ in Occupations:
                            house_info[occ_pos_local[occ]]['Occupation'] = occ

                        # Verify completeness
                        complete = True
                        for h in houses:
                            if set(house_info[h].keys()) != {'Name', 'Nationality', 'Vacation', 'Education', 'Occupation'}:
                                complete = False
                                break
                        if not complete:
                            continue

                        solutions.append(house_info)
                        success_nat = True
                        break  # If one nationality assignment works, we can stop trying others
                    if success_nat:
                        break  # Found valid nationality for this occupation assignment
                # If solution found, no need to continue deeper
            # End education loop
        # End city loop
    # End names loop

    if not solutions:
        raise RuntimeError("No solution found")

    # Assuming unique solution
    sol = solutions[0]
    # Prepare JSON output
    header = ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"]
    rows = []
    for h in houses:
        row = [str(h), sol[h]['Name'], sol[h]['Nationality'], sol[h]['Vacation'], sol[h]['Education'], sol[h]['Occupation']]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))