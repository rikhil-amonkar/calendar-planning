import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define enums for attributes
    Name = z3.EnumSort('Name', ['Eric', 'Arnold'])
    Mother = z3.EnumSort('Mother', ['Aniya', 'Holly'])
    CarModel = z3.EnumSort('CarModel', ['ford f150', 'tesla model 3'])
    Height = z3.EnumSort('Height', ['short', 'very short'])
    
    # Create constants for enum values
    Eric, Arnold = Name.consts()
    Aniya, Holly = Mother.consts()
    ford_f150, tesla_model_3 = CarModel.consts()
    short, very_short = Height.consts()
    
    # Create variables for each house
    houses = [0, 1]
    name = [z3.Const(f'name_{i}', Name) for i in houses]
    mother = [z3.Const(f'mother_{i}', Mother) for i in houses]
    car = [z3.Const(f'car_{i}', CarModel) for i in houses]
    height = [z3.Const(f'height_{i}', Height) for i in houses]
    
    # Add uniqueness constraints
    solver.add(z3.Distinct(name))
    solver.add(z3.Distinct(mother))
    solver.add(z3.Distinct(car))
    solver.add(z3.Distinct(height))
    
    # Clue 1: Tesla Model 3 is right of Arnold
    arnold_house = z3.Int('arnold_house')
    solver.add(arnold_house == z3.If(name[0] == Arnold, 0, 1))
    tesla_house = z3.Int('tesla_house')
    solver.add(tesla_house == z3.If(car[0] == tesla_model_3, 0, 1))
    solver.add(tesla_house > arnold_house)
    
    # Clue 2: Arnold is short
    solver.add(z3.Implies(name[0] == Arnold, height[0] == short))
    solver.add(z3.Implies(name[1] == Arnold, height[1] == short))
    
    # Clue 3: Mother Holly is in second house
    solver.add(mother[1] == Holly)
    
    # Check solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in houses:
            n_val = model.eval(name[i])
            m_val = model.eval(mother[i])
            c_val = model.eval(car[i])
            h_val = model.eval(height[i])
            
            # Convert Z3 symbols to strings
            n_str = str(n_val)
            m_str = str(m_val)
            c_str = str(c_val)
            h_str = str(h_val)
            
            rows.append([str(i+1), n_str, m_str, c_str, h_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()