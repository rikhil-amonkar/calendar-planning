import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the attributes using EnumSort for better readability and debugging
    House = [1, 2, 3, 4]  # We'll use integers for houses, but we need to model attributes
    NameSort, names = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice'])
    SmoothieSort, smoothies = EnumSort('Smoothie', ['dragonfruit', 'cherry', 'desert', 'watermelon'])
    CigarSort, cigars = EnumSort('Cigar', ['blue master', 'pall mall', 'dunhill', 'prince'])
    HeightSort, heights = EnumSort('Height', ['tall', 'average', 'short', 'very short'])
    PhoneSort, phones = EnumSort('Phone', ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9'])

    # Create variables for each house for each attribute
    name_vars = [Const(f'name_{i}', NameSort) for i in range(1,5)]
    smoothie_vars = [Const(f'smoothie_{i}', SmoothieSort) for i in range(1,5)]
    cigar_vars = [Const(f'cigar_{i}', CigarSort) for i in range(1,5)]
    height_vars = [Const(f'height_{i}', HeightSort) for i in range(1,5)]
    phone_vars = [Const(f'phone_{i}', PhoneSort) for i in range(1,5)]

    # Each attribute must have distinct values
    solver.add(Distinct(name_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(phone_vars))

    # Helper functions to get the value of an attribute for a house
    def get_name(house):
        return name_vars[house-1]
    def get_smoothie(house):
        return smoothie_vars[house-1]
    def get_cigar(house):
        return cigar_vars[house-1]
    def get_height(house):
        return height_vars[house-1]
    def get_phone(house):
        return phone_vars[house-1]

    # Define the constants for each value in the enums
    Eric, Peter, Arnold, Alice = names
    dragonfruit, cherry, desert, watermelon = smoothies
    blue_master, pall_mall, dunhill, prince = cigars
    tall, average, short, very_short = heights
    google_pixel_6, samsung_galaxy_s21, iphone_13, oneplus_9 = phones

    # Add constraints from the clues
    # 1. The Dragonfruit smoothie lover is Eric.
    solver.add(get_smoothie(1) == dragonfruit, get_name(1) == Eric)
    solver.add(get_smoothie(2) == dragonfruit, get_name(2) == Eric)
    solver.add(get_smoothie(3) == dragonfruit, get_name(3) == Eric)
    solver.add(get_smoothie(4) == dragonfruit, get_name(4) == Eric)
    # Actually, we should find which house has dragonfruit and Eric and equate them
    # Instead, we do: For some house i, smoothie(i)=dragonfruit and name(i)=Eric
    # But since attributes are unique, we can use:
    solver.add(Or([And(get_smoothie(i) == dragonfruit, get_name(i) == Eric) for i in range(1,5)]))

    # 2. The Dunhill smoker is the person who likes Cherry smoothies.
    solver.add(Or([And(get_cigar(i) == dunhill, get_smoothie(i) == cherry) for i in range(1,5)]))

    # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    solver.add(Or([And(get_phone(i) == samsung_galaxy_s21, get_phone(i+1) == iphone_13) for i in range(1,4)]))

    # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
    # This means there exists i<j such that height(i)=very_short and cigar(j)=dunhill
    solver.add(Or([And(get_height(i) == very_short, get_cigar(j) == dunhill, i < j) for i in range(1,5) for j in range(1,5) if i < j]))

    # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    solver.add(Or([And(get_smoothie(i) == desert, get_smoothie(j) == watermelon, i < j) for i in range(1,5) for j in range(1,5) if i < j]))

    # 6. The Prince smoker is the person who uses a OnePlus 9.
    solver.add(Or([And(get_cigar(i) == prince, get_phone(i) == oneplus_9) for i in range(1,5)]))

    # 7. The person who is tall is in the third house.
    solver.add(get_height(3) == tall)

    # 8. The person who is very short is the person who uses an iPhone 13.
    solver.add(Or([And(get_height(i) == very_short, get_phone(i) == iphone_13) for i in range(1,5)]))

    # 9. The person who smokes Blue Master is not in the first house.
    solver.add(get_cigar(1) != blue_master)

    # 10. The Dunhill smoker is the person who is short.
    solver.add(Or([And(get_cigar(i) == dunhill, get_height(i) == short) for i in range(1,5)]))

    # 11. Peter is not in the third house.
    solver.add(get_name(3) != Peter)

    # 12. Arnold is the person who uses a Google Pixel 6.
    solver.add(Or([And(get_name(i) == Arnold, get_phone(i) == google_pixel_6) for i in range(1,5)]))

    # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
    solver.add(Or([And(get_smoothie(i) == dragonfruit, get_cigar(i) == pall_mall) for i in range(1,5)]))

    # Check if the solver is satisfied and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the result structure
        header = ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"]
        rows = []
        
        # For each house, get the value of each attribute from the model
        for house in range(1,5):
            name_val = model.eval(get_name(house))
            smoothie_val = model.eval(get_smoothie(house))
            cigar_val = model.eval(get_cigar(house))
            height_val = model.eval(get_height(house))
            phone_val = model.eval(get_phone(house))
            
            # Convert the Z3 values to strings
            row = [
                str(house),
                str(name_val),
                str(smoothie_val),
                str(cigar_val),
                str(height_val),
                str(phone_val)
            ]
            rows.append(row)
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output the JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()