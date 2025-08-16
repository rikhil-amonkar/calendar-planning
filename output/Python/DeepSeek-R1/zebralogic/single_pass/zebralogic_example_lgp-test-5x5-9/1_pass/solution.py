import json

class Solver:
    def __init__(self):
        self.attributes = ['Name', 'Drink', 'Color', 'Flower', 'Hobby']
        self.domains = {
            'Name': set(['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']),
            'Drink': set(['milk', 'root beer', 'coffee', 'tea', 'water']),
            'Color': set(['blue', 'green', 'white', 'yellow', 'red']),
            'Flower': set(['daffodils', 'roses', 'lilies', 'tulips', 'carnations']),
            'Hobby': set(['painting', 'cooking', 'photography', 'gardening', 'knitting'])
        }
        self.grid = [ {attr: None for attr in self.attributes} for _ in range(5)]
        self.house_domains = [ {attr: set(self.domains[attr]) for attr in self.attributes} for _ in range(5)]
        
        # Set fixed assignments from clues
        self.set_value(1, 'Color', 'white')   # Clue15
        self.set_value(1, 'Flower', 'roses')  # Clue10 and Clue15
        self.set_value(2, 'Drink', 'water')   # Clue13
        self.set_value(2, 'Name', 'Peter')    # Clue8 and Clue13
        self.set_value(0, 'Name', 'Eric')     # Clue7 and deduction
        self.set_value(1, 'Drink', 'tea')     # Clue7 and deduction

    def set_value(self, house_index, attribute, value):
        self.grid[house_index][attribute] = value
        for i in range(5):
            if i != house_index and value in self.house_domains[i][attribute]:
                self.house_domains[i][attribute].remove(value)
        self.house_domains[house_index][attribute] = set([value])
    
    def is_complete(self):
        for house in self.grid:
            for attr in self.attributes:
                if house[attr] is None:
                    return False
        return True

    def get_unassigned_variable(self):
        min_domain_size = float('inf')
        best = None
        for i in range(5):
            for attr in self.attributes:
                if self.grid[i][attr] is None:
                    domain_size = len(self.house_domains[i][attr])
                    if domain_size < min_domain_size:
                        min_domain_size = domain_size
                        best = (i, attr)
        return best

    def check_constraints(self):
        # Clue1: Alice not in fourth house (index3)
        if self.grid[3]['Name'] == 'Alice':
            return False
        
        # Clue2: root beer drinker enjoys gardening
        for i in range(5):
            if self.grid[i]['Drink'] == 'root beer' and self.grid[i]['Hobby'] is not None and self.grid[i]['Hobby'] != 'gardening':
                return False
            if self.grid[i]['Hobby'] == 'gardening' and self.grid[i]['Drink'] is not None and self.grid[i]['Drink'] != 'root beer':
                return False
        
        # Clue3: green color is coffee drinker
        for i in range(5):
            if self.grid[i]['Color'] == 'green' and self.grid[i]['Drink'] is not None and self.grid[i]['Drink'] != 'coffee':
                return False
            if self.grid[i]['Drink'] == 'coffee' and self.grid[i]['Color'] is not None and self.grid[i]['Color'] != 'green':
                return False
        
        # Clue4: green color loves lilies
        for i in range(5):
            if self.grid[i]['Color'] == 'green' and self.grid[i]['Flower'] is not None and self.grid[i]['Flower'] != 'lilies':
                return False
            if self.grid[i]['Flower'] == 'lilies' and self.grid[i]['Color'] is not None and self.grid[i]['Color'] != 'green':
                return False
        
        # Clue5: blue color right of daffodils
        daffodils_house = None
        blue_house = None
        for i in range(5):
            if self.grid[i]['Flower'] == 'daffodils':
                daffodils_house = i
            if self.grid[i]['Color'] == 'blue':
                blue_house = i
        if daffodils_house is not None and blue_house is not None and blue_house <= daffodils_house:
            return False
        
        # Clue6: cooking hobby has blue color
        for i in range(5):
            if self.grid[i]['Hobby'] == 'cooking' and self.grid[i]['Color'] is not None and self.grid[i]['Color'] != 'blue':
                return False
            if self.grid[i]['Color'] == 'blue' and self.grid[i]['Hobby'] is not None and self.grid[i]['Hobby'] != 'cooking':
                return False
        
        # Clue7: Eric directly left of tea drinker
        eric_house = None
        tea_house = None
        for i in range(5):
            if self.grid[i]['Name'] == 'Eric':
                eric_house = i
            if self.grid[i]['Drink'] == 'tea':
                tea_house = i
        if eric_house is not None and tea_house is not None and tea_house - eric_house != 1:
            return False
        
        # Clue8: water drinker is Peter
        for i in range(5):
            if self.grid[i]['Drink'] == 'water' and self.grid[i]['Name'] is not None and self.grid[i]['Name'] != 'Peter':
                return False
            if self.grid[i]['Name'] == 'Peter' and self.grid[i]['Drink'] is not None and self.grid[i]['Drink'] != 'water':
                return False
        
        # Clue9: Arnold is photography
        for i in range(5):
            if self.grid[i]['Name'] == 'Arnold' and self.grid[i]['Hobby'] is not None and self.grid[i]['Hobby'] != 'photography':
                return False
            if self.grid[i]['Hobby'] == 'photography' and self.grid[i]['Name'] is not None and self.grid[i]['Name'] != 'Arnold':
                return False
        
        # Clue10: white color loves roses
        for i in range(5):
            if self.grid[i]['Color'] == 'white' and self.grid[i]['Flower'] is not None and self.grid[i]['Flower'] != 'roses':
                return False
            if self.grid[i]['Flower'] == 'roses' and self.grid[i]['Color'] is not None and self.grid[i]['Color'] != 'white':
                return False
        
        # Clue11: one house between carnations and red color
        carnations_house = None
        red_house = None
        for i in range(5):
            if self.grid[i]['Flower'] == 'carnations':
                carnations_house = i
            if self.grid[i]['Color'] == 'red':
                red_house = i
        if carnations_house is not None and red_house is not None and abs(carnations_house - red_house) != 2:
            return False
        
        # Clue12: cooking left of painting
        cooking_house = None
        painting_house = None
        for i in range(5):
            if self.grid[i]['Hobby'] == 'cooking':
                cooking_house = i
            if self.grid[i]['Hobby'] == 'painting':
                painting_house = i
        if cooking_house is not None and painting_house is not None and cooking_house >= painting_house:
            return False
        
        # Clue13: water in third house
        if self.grid[2]['Drink'] is not None and self.grid[2]['Drink'] != 'water':
            return False
        for i in range(5):
            if i != 2 and self.grid[i]['Drink'] == 'water':
                return False
        
        # Clue14: carnations is root beer
        for i in range(5):
            if self.grid[i]['Flower'] == 'carnations' and self.grid[i]['Drink'] is not None and self.grid[i]['Drink'] != 'root beer':
                return False
            if self.grid[i]['Drink'] == 'root beer' and self.grid[i]['Flower'] is not None and self.grid[i]['Flower'] != 'carnations':
                return False
        
        # Clue15: white in second house
        if self.grid[1]['Color'] is not None and self.grid[1]['Color'] != 'white':
            return False
        for i in range(5):
            if i != 1 and self.grid[i]['Color'] == 'white':
                return False
        
        return True

    def solve(self):
        if self.is_complete():
            if self.check_constraints():
                return True
            else:
                return False
        
        next_var = self.get_unassigned_variable()
        if next_var is None:
            return False
        
        house_index, attribute = next_var
        saved_house_domains = [ {a: set(dom) for a, dom in house.items()} for house in self.house_domains]
        saved_grid = [ dict(house) for house in self.grid ]
        
        for value in list(self.house_domains[house_index][attribute]):
            self.grid[house_index][attribute] = value
            old_domains = {}
            for i in range(5):
                if i != house_index and value in self.house_domains[i][attribute]:
                    old_domains[i] = self.house_domains[i][attribute].copy()
                    self.house_domains[i][attribute].discard(value)
            old_domain_here = self.house_domains[house_index][attribute]
            self.house_domains[house_index][attribute] = set([value])
            
            if self.check_constraints():
                if self.solve():
                    return True
            
            self.grid[house_index][attribute] = None
            for i in range(5):
                if i in old_domains:
                    self.house_domains[i][attribute] = old_domains[i]
            self.house_domains[house_index][attribute] = old_domain_here
        
        for i in range(5):
            self.grid[i] = saved_grid[i]
            for attr in self.attributes:
                self.house_domains[i][attr] = saved_house_domains[i][attr]
                
        return False

def main():
    solver = Solver()
    if solver.solve():
        header = ["House", "Name", "Drink", "Color", "Flower", "Hobby"]
        rows = []
        for i in range(5):
            house_data = [str(i+1)]
            for attr in ['Name', 'Drink', 'Color', 'Flower', 'Hobby']:
                house_data.append(solver.grid[i][attr])
            rows.append(house_data)
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()