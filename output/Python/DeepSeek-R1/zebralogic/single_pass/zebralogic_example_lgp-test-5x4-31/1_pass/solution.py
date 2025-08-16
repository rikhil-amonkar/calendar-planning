import itertools
import json

def main():
    names_options = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacation_options = ['city', 'camping', 'beach', 'mountain']
    children_options = ['Bella', 'Samantha', 'Fred', 'Timothy']
    nationality_options = ['norwegian', 'brit', 'german', 'swede']
    
    found_solution = None
    
    for names in itertools.permutations(names_options):
        if names[4] == 'Eric':  # Clue 8: Eric not in fifth house (index4)
            continue
            
        for vacations in itertools.permutations(vacation_options):
            vacation_list = ['cruise'] + list(vacations)  # Clue 6: first house cruise
            
            if vacation_list[4] == 'camping':  # Clue 13: camping not in fifth house
                continue
                
            for children in itertools.permutations(children_options):
                children_list = [
                    children[0],
                    children[1],
                    children[2],
                    'Meredith',  # Clue 7: Meredith in fourth house (index3)
                    children[3]
                ]
                
                if children_list[1] == 'Bella':  # Clue 4: Bella not in second house (index1)
                    continue
                    
                for nationalities in itertools.permutations(nationality_options):
                    nationality_list = list(nationalities) + ['dane']  # Clue 12: Dane in fifth house (index4)
                    
                    # Clue 1: Peter is Norwegian
                    if 'Peter' not in names:
                        continue
                    peter_index = names.index('Peter')
                    if peter_index == 4:  # Peter cannot be in house5 (dane) and also norwegian
                        continue
                    if nationality_list[peter_index] != 'norwegian':
                        continue
                    
                    # Clue 2: Swedish person has child Bella
                    if 'swede' not in nationality_list[:4]:
                        continue
                    swede_index = nationality_list.index('swede')
                    if children_list[swede_index] != 'Bella':
                        continue
                    
                    # Clue 3: Beach vacation directly left of Samantha child
                    found_beach = False
                    for i in range(4):  # i from 0 to 3 (house1 to house4)
                        if vacation_list[i] == 'beach' and children_list[i+1] == 'Samantha':
                            found_beach = True
                            break
                    if not found_beach:
                        continue
                    
                    # Clue 5: Alice is British
                    if 'Alice' not in names:
                        continue
                    alice_index = names.index('Alice')
                    if alice_index == 4:  # Alice cannot be in house5 (dane) and brit
                        continue
                    if nationality_list[alice_index] != 'brit':
                        continue
                    
                    # Clue 9: Swedish to the right of Norwegian (Peter)
                    if swede_index <= peter_index:
                        continue
                    
                    # Clue 10: One house between Fred and city vacation
                    if 'Fred' not in children_list:
                        continue
                    fred_index = children_list.index('Fred')
                    if 'city' not in vacation_list:
                        continue
                    city_index = vacation_list.index('city')
                    if abs(fred_index - city_index) != 2:
                        continue
                    
                    # Clue 11: Bob has camping vacation
                    if 'Bob' not in names:
                        continue
                    bob_index = names.index('Bob')
                    if vacation_list[bob_index] != 'camping':
                        continue
                    
                    # All clues satisfied, build solution
                    rows = []
                    for i in range(5):
                        rows.append([
                            str(i+1),        # House number
                            names[i],        # Name
                            vacation_list[i],# Vacation
                            children_list[i],# Children
                            nationality_list[i] # Nationality
                        ])
                    
                    solution = {
                        "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                        "rows": rows
                    }
                    found_solution = solution
                    break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution:
        output = {"solution": found_solution}
    else:
        output = {"error": "No solution found"}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()