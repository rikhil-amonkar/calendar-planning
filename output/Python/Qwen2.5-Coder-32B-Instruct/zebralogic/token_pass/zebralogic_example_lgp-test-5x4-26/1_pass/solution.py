import json

def solve_puzzle():
    # Initialize the houses with empty attributes
    houses = [{'Name': None, 'Height': None, 'Mother': None, 'HairColor': None} for _ in range(5)]
    
    # Lists of possible values for each attribute
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    # Unassigned sets for each attribute
    unassigned_names = set(names)
    unassigned_heights = set(heights)
    unassigned_mothers = set(mothers)
    unassigned_hair_colors = set(hair_colors)
    
    # Constraint helper functions
    def constraint_1():
        for house in houses:
            if house['Height'] == 'tall' and house['Mother'] == 'Holly':
                return True
        return False
    
    def constraint_2():
        for i in range(len(houses) - 2):
            if (houses[i]['Height'] == 'average' and houses[i+2]['Height'] == 'short') or \
               (houses[i]['Height'] == 'short' and houses[i+2]['Height'] == 'average'):
                return True
        return False
    
    def constraint_3():
        for i in range(len(houses) - 1):
            if houses[i]['HairColor'] == 'gray' and houses[i+1]['Mother'] == 'Janelle':
                return True
        return False
    
    def constraint_4():
        for house in houses:
            if house['HairColor'] == 'black' and house['Name'] != 'Eric' and house['Name'] != 'Bob':
                return False
        return True
    
    def constraint_5():
        for house in houses:
            if house['Name'] == 'Eric' and house['HairColor'] == 'black':
                return True
        return False
    
    def constraint_6():
        for house in houses:
            if house['Height'] == 'very short' and house['Mother'] == 'Penny':
                return True
        return False
    
    def constraint_7():
        for i in range(len(houses) - 1):
            if (houses[i]['HairColor'] == 'gray' and houses[i+1]['Name'] == 'Eric') or \
               (houses[i]['Name'] == 'Eric' and houses[i+1]['HairColor'] == 'gray'):
                return True
        return False
    
    def constraint_8():
        return houses[4]['Name'] == 'Bob'
    
    def constraint_9():
        for house in houses:
            if house['Name'] == 'Peter' and house['HairColor'] == 'red':
                return True
        return False
    
    def constraint_10():
        for i in range(len(houses) - 1):
            if houses[i]['Mother'] == 'Kailyn' and houses[i+1]['Height'] == 'short':
                return True
        return False
    
    def constraint_11():
        for house in houses:
            if house['Name'] == 'Arnold' and house['HairColor'] == 'brown':
                return True
        return False
    
    def constraint_12():
        for i in range(len(houses) - 1):
            if houses[i]['HairColor'] == 'brown' and houses[i+1]['Mother'] == 'Janelle':
                return True
        return False
    
    def constraint_13():
        for i in range(len(houses) - 1):
            if (houses[i]['Mother'] == 'Aniya' and houses[i+1]['Height'] == 'very short') or \
               (houses[i]['Height'] == 'very short' and houses[i+1]['Mother'] == 'Aniya'):
                return True
        return False
    
    def constraint_14():
        return houses[2]['Mother'] == 'Kailyn'
    
    # Backtracking function
    def backtrack(house_index):
        if house_index == 5:
            # Check all constraints
            if constraint_1() and constraint_2() and constraint_3() and constraint_4() and constraint_5() and \
               constraint_6() and constraint_7() and constraint_8() and constraint_9() and constraint_10() and \
               constraint_11() and constraint_12() and constraint_13() and constraint_14():
                return True
            else:
                return False
        
        for name in list(unassigned_names):
            for height in list(unassigned_heights):
                for mother in list(unassigned_mothers):
                    for hair_color in list(unassigned_hair_colors):
                        houses[house_index] = {'Name': name, 'Height': height, 'Mother': mother, 'HairColor': hair_color}
                        unassigned_names.remove(name)
                        unassigned_heights.remove(height)
                        unassigned_mothers.remove(mother)
                        unassigned_hair_colors.remove(hair_color)
                        
                        if backtrack(house_index + 1):
                            return True
                        
                        # Backtrack
                        houses[house_index] = {'Name': None, 'Height': None, 'Mother': None, 'HairColor': None}
                        unassigned_names.add(name)
                        unassigned_heights.add(height)
                        unassigned_mothers.add(mother)
                        unassigned_hair_colors.add(hair_color)
        
        return False
    
    # Start the backtracking process
    if backtrack(0):
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": [[str(i+1), house['Name'], house['Height'], house['Mother'], house['HairColor']] for i, house in enumerate(houses)]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

solve_puzzle()