import json

def main():
    # Define the initial domains
    initial_domains = {
        'Name': ['Alice', 'Peter', 'Arnold', 'Eric'],
        'Mother': ['Holly', 'Kailyn', 'Janelle', 'Aniya'],
        'Flower': ['carnations', 'roses', 'lilies', 'daffodils']
    }
    
    # Initialize the state with fixed assignments
    state = [
        {'Name': None, 'Mother': None, 'Flower': None},
        {'Name': None, 'Mother': None, 'Flower': 'lilies'},
        {'Name': 'Alice', 'Mother': 'Kailyn', 'Flower': None},
        {'Name': None, 'Mother': None, 'Flower': None}
    ]
    
    # Define constraints as functions
    def constraint2(state):
        arnold_house = None
        janelle_house = None
        for i, house in enumerate(state):
            if house['Name'] == 'Arnold':
                arnold_house = i
            if house['Mother'] == 'Janelle':
                janelle_house = i
        if arnold_house is None or janelle_house is None:
            return True
        return janelle_house > arnold_house

    def constraint3(state):
        carnations_house = None
        peter_house = None
        for i, house in enumerate(state):
            if house['Flower'] == 'carnations':
                carnations_house = i
            if house['Name'] == 'Peter':
                peter_house = i
        if carnations_house is None or peter_house is None:
            return True
        return peter_house > carnations_house

    def constraint4(state):
        for i, house in enumerate(state):
            if house['Name'] == 'Eric' and house['Flower'] is not None and house['Flower'] != 'daffodils':
                return False
            if house['Flower'] == 'daffodils' and house['Name'] is not None and house['Name'] != 'Eric':
                return False
        return True

    def constraint5(state):
        for i, house in enumerate(state):
            if house['Name'] == 'Arnold' and house['Mother'] is not None and house['Mother'] != 'Holly':
                return False
            if house['Mother'] == 'Holly' and house['Name'] is not None and house['Name'] != 'Arnold':
                return False
        return True

    def constraint6(state):
        holly_house = None
        carnations_house = None
        for i, house in enumerate(state):
            if house['Mother'] == 'Holly':
                holly_house = i
            if house['Flower'] == 'carnations':
                carnations_house = i
        if holly_house is None or carnations_house is None:
            return True
        return carnations_house > holly_house

    constraints = [constraint2, constraint3, constraint4, constraint5, constraint6]
    
    def is_complete(state):
        for house in state:
            if house['Name'] is None or house['Mother'] is None or house['Flower'] is None:
                return False
        return True
    
    def backtrack(state):
        if is_complete(state):
            return state
        
        for i, house in enumerate(state):
            for attribute in ['Name', 'Mother', 'Flower']:
                if state[i][attribute] is None:
                    used_values = {h[attribute] for h in state if h[attribute] is not None}
                    available = set(initial_domains[attribute]) - used_values
                    for value in available:
                        state[i][attribute] = value
                        if all(constraint(state) for constraint in constraints):
                            result = backtrack(state)
                            if result is not None:
                                return result
                        state[i][attribute] = None
                    return None
        return None
    
    solution_state = backtrack(state)
    
    if solution_state is None:
        print("No solution found")
        return
    
    # Format the solution as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": []
        }
    }
    
    for i, house in enumerate(solution_state):
        house_number = str(i + 1)
        output["solution"]["rows"].append([
            house_number,
            house['Name'],
            house['Mother'],
            house['Flower']
        ])
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()