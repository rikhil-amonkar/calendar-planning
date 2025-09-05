import z3
import json

def main():
    # Define the sorts for each attribute
    Name, (Alice, Peter, Arnold, Eric) = z3.EnumSort('Name', ['Alice', 'Peter', 'Arnold', 'Eric'])
    Mother, (Holly, Kailyn, Janelle, Aniya) = z3.EnumSort('Mother', ['Holly', 'Kailyn', 'Janelle', 'Aniya'])
    Flower, (carnations, roses, lilies, daffodils) = z3.EnumSort('Flower', ['carnations', 'roses', 'lilies', 'daffodils'])
    
    # Create variables for each house
    houses = [0, 1, 2, 3]  # Representing house numbers 1 to 4
    n = [z3.Const(f'n_{i}', Name) for i in houses]
    m = [z3.Const(f'm_{i}', Mother) for i in houses]
    f = [z3.Const(f'f_{i}', Flower) for i in houses]
    
    s = z3.Solver()
    
    # Each attribute must be unique per house
    s.add(z3.Distinct(n))
    s.add(z3.Distinct(m))
    s.add(z3.Distinct(f))
    
    # Clue 8: Alice is in the third house (index 2)
    s.add(n[2] == Alice)
    
    # Clue 1: Alice is the person whose mother's name is Kailyn
    s.add(z3.ForAll([n[2], m[2]], z3.Implies(n[2] == Alice, m[2] == Kailyn)))
    
    # Clue 2: The person whose mother's name is Janelle is right of Arnold
    arnold_idx = z3.Int('arnold_idx')
    janelle_m_idx = z3.Int('janelle_m_idx')
    s.add(arnold_idx >= 0, arnold_idx <= 3)
    s.add(janelle_m_idx >= 0, janelle_m_idx <= 3)
    for i in houses:
        s.add(z3.Implies(n[i] == Arnold, arnold_idx == i))
        s.add(z3.Implies(m[i] == Janelle, janelle_m_idx == i))
    s.add(janelle_m_idx > arnold_idx)
    
    # Clue 3: Peter is right of the person who loves carnations
    peter_idx = z3.Int('peter_idx')
    carnations_idx = z3.Int('carnations_idx')
    s.add(peter_idx >= 0, peter_idx <= 3)
    s.add(carnations_idx >= 0, carnations_idx <= 3)
    for i in houses:
        s.add(z3.Implies(n[i] == Peter, peter_idx == i))
        s.add(z3.Implies(f[i] == carnations, carnations_idx == i))
    s.add(peter_idx > carnations_idx)
    
    # Clue 4: Eric loves daffodils
    for i in houses:
        s.add(z3.Implies(n[i] == Eric, f[i] == daffodils))
    
    # Clue 5: Arnold's mother is Holly
    for i in houses:
        s.add(z3.Implies(n[i] == Arnold, m[i] == Holly))
    
    # Clue 6: Carnations lover is right of Holly mother
    holly_m_idx = z3.Int('holly_m_idx')
    s.add(holly_m_idx >= 0, holly_m_idx <= 3)
    for i in houses:
        s.add(z3.Implies(m[i] == Holly, holly_m_idx == i))
    s.add(carnations_idx > holly_m_idx)
    
    # Clue 7: Lilies lover is directly left of Alice
    lilies_idx = z3.Int('lilies_idx')
    s.add(lilies_idx >= 0, lilies_idx <= 3)
    for i in houses:
        s.add(z3.Implies(f[i] == lilies, lilies_idx == i))
    s.add(lilies_idx == 1)  # Since Alice is at index 2 (house 3), left is index 1 (house 2)
    
    # Check and get the model
    if s.check() == z3.sat:
        model = s.model()
        
        # Map house indices to attribute values
        result = []
        attr_map = {
            Name: ['Alice', 'Peter', 'Arnold', 'Eric'],
            Mother: ['Holly', 'Kailyn', 'Janelle', 'Aniya'],
            Flower: ['carnations', 'roses', 'lilies', 'daffodils']
        }
        
        for i in houses:
            name_val = model.eval(n[i])
            mother_val = model.eval(m[i])
            flower_val = model.eval(f[i])
            
            # Convert Z3 values to strings using the mapping
            name_str = attr_map[Name][name_val.as_long()]
            mother_str = attr_map[Mother][mother_val.as_long()]
            flower_str = attr_map[Flower][flower_val.as_long()]
            
            result.append([str(i+1), name_str, mother_str, flower_str])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()