import json
from z3 import *

def main():
    # Define the attributes
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    
    # Create Z3 enum sorts for each attribute
    NameSort, name_consts = EnumSort('Name', names)
    VacationSort, vacation_consts = EnumSort('Vacation', vacations)
    ChildSort, child_consts = EnumSort('Child', children)
    NationalitySort, nationality_consts = EnumSort('Nationality', nationalities)
    
    # Create mappings from string names to Z3 constants
    name_dict = dict(zip(names, name_consts))
    vacation_dict = dict(zip(vacations, vacation_consts))
    child_dict = dict(zip(children, child_consts))
    nationality_dict = dict(zip(nationalities, nationality_consts))
    
    # Create variables for each house (1-5) for each attribute
    houses = [1, 2, 3, 4, 5]
    name_vars = [Const(f'name_{i}', NameSort) for i in houses]
    vacation_vars = [Const(f'vacation_{i}', VacationSort) for i in houses]
    child_vars = [Const(f'child_{i}', ChildSort) for i in houses]
    nationality_vars = [Const(f'nationality_{i}', NationalitySort) for i in houses]
    
    solver = Solver()
    
    # Each attribute must be one of the defined values
    for i in houses:
        solver.add(Or([name_vars[i-1] == name_dict[n] for n in names]))
        solver.add(Or([vacation_vars[i-1] == vacation_dict[v] for v in vacations]))
        solver.add(Or([child_vars[i-1] == child_dict[c] for c in children]))
        solver.add(Or([nationality_vars[i-1] == nationality_dict[nat] for nat in nationalities]))
    
    # All attributes are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(vacation_vars))
    solver.add(Distinct(child_vars))
    solver.add(Distinct(nationality_vars))
    
    # Add constraints from clues
    # 1. The Norwegian is Peter.
    for i in houses:
        solver.add(Implies(nationality_vars[i-1] == nationality_dict['norwegian'], name_vars[i-1] == name_dict['Peter']))
    
    # 2. The Swedish person is the person's child is named Bella.
    for i in houses:
        solver.add(Implies(nationality_vars[i-1] == nationality_dict['swede'], child_vars[i-1] == child_dict['Bella']))
    
    # 3. The person who loves beach vacations is directly left of the person's child is named Samantha.
    for i in range(1, 5):
        solver.add(Implies(vacation_vars[i-1] == vacation_dict['beach'], child_vars[i] == child_dict['Samantha']))
    
    # 4. The person's child is named Bella is not in the second house.
    solver.add(child_vars[1] != child_dict['Bella'])
    
    # 5. Alice is the British person.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_dict['Alice'], nationality_vars[i-1] == nationality_dict['brit']))
    
    # 6. The person who likes going on cruises is in the first house.
    solver.add(vacation_vars[0] == vacation_dict['cruise'])
    
    # 7. The person's child is named Meredith is in the fourth house.
    solver.add(child_vars[3] == child_dict['Meredith'])
    
    # 8. Eric is not in the fifth house.
    solver.add(name_vars[4] != name_dict['Eric'])
    
    # 9. The Swedish person is somewhere to the right of the Norwegian.
    norwegian_index = Int('norwegian_index')
    swede_index = Int('swede_index')
    solver.add(norwegian_index >= 1, norwegian_index <= 5)
    solver.add(swede_index >= 1, swede_index <= 5)
    for i in houses:
        solver.add(Implies(nationality_vars[i-1] == nationality_dict['norwegian'], norwegian_index == i))
        solver.add(Implies(nationality_vars[i-1] == nationality_dict['swede'], swede_index == i))
    solver.add(swede_index > norwegian_index)
    
    # 10. There is one house between the person's child is named Fred and the person who prefers city breaks.
    fred_index = Int('fred_index')
    city_index = Int('city_index')
    solver.add(fred_index >= 1, fred_index <= 5)
    solver.add(city_index >= 1, city_index <= 5)
    for i in houses:
        solver.add(Implies(child_vars[i-1] == child_dict['Fred'], fred_index == i))
        solver.add(Implies(vacation_vars[i-1] == vacation_dict['city'], city_index == i))
    solver.add(Or(fred_index - city_index == 2, city_index - fred_index == 2))
    
    # 11. Bob is the person who enjoys camping trips.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_dict['Bob'], vacation_vars[i-1] == vacation_dict['camping']))
    
    # 12. The Dane is in the fifth house.
    solver.add(nationality_vars[4] == nationality_dict['dane'])
    
    # 13. The person who enjoys camping trips is not in the fifth house.
    solver.add(vacation_vars[4] != vacation_dict['camping'])
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Create reverse mappings for interpretation
        rev_name = {v: k for k, v in name_dict.items()}
        rev_vacation = {v: k for k, v in vacation_dict.items()}
        rev_child = {v: k for k, v in child_dict.items()}
        rev_nationality = {v: k for k, v in nationality_dict.items()}
        
        # Extract values
        result = []
        for i in houses:
            name_val = model.eval(name_vars[i-1])
            vacation_val = model.eval(vacation_vars[i-1])
            child_val = model.eval(child_vars[i-1])
            nationality_val = model.eval(nationality_vars[i-1])
            
            result.append([
                str(i),
                rev_name[name_val],
                rev_vacation[vacation_val],
                rev_child[child_val],
                rev_nationality[nationality_val]
            ])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()