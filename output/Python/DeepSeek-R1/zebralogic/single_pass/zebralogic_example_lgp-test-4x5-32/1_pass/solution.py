import json

def main():
    attributes = ['Name', 'Hobby', 'Birthday', 'Education', 'Smoothie']
    domains = {
        'Name': set(['Arnold', 'Alice', 'Eric', 'Peter']),
        'Hobby': set(['cooking', 'painting', 'photography', 'gardening']),
        'Birthday': set(['april', 'jan', 'sept', 'feb']),
        'Education': set(['master', 'bachelor', 'associate', 'high school']),
        'Smoothie': set(['cherry', 'watermelon', 'desert', 'dragonfruit'])
    }
    
    state = [None, None, None, None]
    
    def check_state(state):
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Smoothie'] == 'desert' and house['Birthday'] != 'jan':
                return False
            if house['Birthday'] == 'jan' and house['Smoothie'] != 'desert':
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Name'] == 'Eric' and house['Education'] != 'bachelor':
                return False
            if house['Education'] == 'bachelor' and house['Name'] != 'Eric':
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Birthday'] == 'jan' and house['Education'] != 'bachelor':
                return False
            if house['Education'] == 'bachelor' and house['Birthday'] != 'jan':
                return False
        
        if state[2] is not None and state[2]['Education'] != 'high school':
            return False
        for i in [0, 1, 3]:
            if state[i] is not None and state[i]['Education'] == 'high school':
                return False
        
        if state[2] is not None and state[2]['Smoothie'] == 'watermelon':
            return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Education'] == 'associate' and house['Name'] != 'Arnold':
                return False
            if house['Name'] == 'Arnold' and house['Education'] != 'associate':
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Education'] == 'master' and house['Hobby'] != 'painting':
                return False
            if house['Hobby'] == 'painting' and house['Education'] != 'master':
                return False
        
        dragonfruit_house = None
        sept_house = None
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Smoothie'] == 'dragonfruit':
                dragonfruit_house = i
            if house['Birthday'] == 'sept':
                sept_house = i
        if dragonfruit_house is not None and sept_house is not None:
            if abs(dragonfruit_house - sept_house) != 2:
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Education'] == 'high school' and house['Birthday'] != 'sept':
                return False
            if house['Birthday'] == 'sept' and house['Education'] != 'high school':
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Hobby'] == 'cooking' and house['Name'] != 'Alice':
                return False
            if house['Name'] == 'Alice' and house['Hobby'] != 'cooking':
                return False
        
        april_house = None
        gardening_house = None
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Birthday'] == 'april':
                april_house = i
            if house['Hobby'] == 'gardening':
                gardening_house = i
        if april_house is not None and gardening_house is not None:
            if abs(april_house - gardening_house) != 1:
                return False
        
        for i, house in enumerate(state):
            if house is None:
                continue
            if house['Hobby'] == 'painting' and house['Birthday'] != 'feb':
                return False
            if house['Birthday'] == 'feb' and house['Hobby'] != 'painting':
                return False
        
        return True

    def backtrack(assignments, remaining_domains, house_index):
        if house_index == 4:
            return assignments
        
        for name in list(remaining_domains['Name']):
            for hobby in list(remaining_domains['Hobby']):
                for birthday in list(remaining_domains['Birthday']):
                    for education in list(remaining_domains['Education']):
                        for smoothie in list(remaining_domains['Smoothie']):
                            house = {
                                'Name': name,
                                'Hobby': hobby,
                                'Birthday': birthday,
                                'Education': education,
                                'Smoothie': smoothie
                            }
                            new_assignments = assignments.copy()
                            new_assignments[house_index] = house
                            
                            if not check_state(new_assignments):
                                continue
                            
                            new_remaining = {
                                'Name': remaining_domains['Name'] - {name},
                                'Hobby': remaining_domains['Hobby'] - {hobby},
                                'Birthday': remaining_domains['Birthday'] - {birthday},
                                'Education': remaining_domains['Education'] - {education},
                                'Smoothie': remaining_domains['Smoothie'] - {smoothie}
                            }
                            
                            result = backtrack(new_assignments, new_remaining, house_index + 1)
                            if result is not None:
                                return result
        return None

    solution_state = backtrack(state, domains, 0)
    
    if solution_state is None:
        print("No solution found")
    else:
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": []
            }
        }
        for idx, house in enumerate(solution_state):
            row = [str(idx + 1), house['Name'], house['Hobby'], house['Birthday'], house['Education'], house['Smoothie']]
            output['solution']['rows'].append(row)
        
        print(json.dumps(output))

if __name__ == "__main__":
    main()