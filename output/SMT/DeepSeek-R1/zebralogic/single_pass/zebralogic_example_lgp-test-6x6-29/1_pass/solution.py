from z3 import *
import json

def main():
    # Define attribute lists
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    house_styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']
    
    # Precompute indices for clarity
    Arnold = names.index('Arnold')
    Carol = names.index('Carol')
    Peter = names.index('Peter')
    Eric = names.index('Eric')
    Bob = names.index('Bob')
    Alice = names.index('Alice')
    
    ranch = house_styles.index('ranch')
    colonial = house_styles.index('colonial')
    modern = house_styles.index('modern')
    craftsman = house_styles.index('craftsman')
    mediterranean = house_styles.index('mediterranean')
    victorian = house_styles.index('victorian')
    
    pizza = foods.index('pizza')
    stew = foods.index('stew')
    spaghetti = foods.index('spaghetti')
    grilled_cheese = foods.index('grilled cheese')
    stir_fry = foods.index('stir fry')
    soup = foods.index('soup')
    
    cultural = vacations.index('cultural')
    cruise = vacations.index('cruise')
    mountain = vacations.index('mountain')
    camping = vacations.index('camping')
    city = vacations.index('city')
    beach = vacations.index('beach')
    
    average = heights.index('average')
    very_tall = heights.index('very tall')
    very_short = heights.index('very short')
    short = heights.index('short')
    tall = heights.index('tall')
    super_tall = heights.index('super tall')
    
    yellow_monster = cigars.index('yellow monster')
    prince = cigars.index('prince')
    dunhill = cigars.index('dunhill')
    pall_mall = cigars.index('pall mall')
    blue_master = cigars.index('blue master')
    blends = cigars.index('blends')
    
    n = 6  # Number of houses
    # Z3 variables for each category per house
    name = [Int('name_%d' % i) for i in range(n)]
    house_style = [Int('hs_%d' % i) for i in range(n)]
    food = [Int('food_%d' % i) for i in range(n)]
    vacation = [Int('vacation_%d' % i) for i in range(n)]
    height = [Int('height_%d' % i) for i in range(n)]
    cigar = [Int('cigar_%d' % i) for i in range(n)]
    
    s = Solver()
    
    # Domain constraints
    for i in range(n):
        s.add(And(name[i] >= 0, name[i] < n))
        s.add(And(house_style[i] >= 0, house_style[i] < n))
        s.add(And(food[i] >= 0, food[i] < n))
        s.add(And(vacation[i] >= 0, vacation[i] < n))
        s.add(And(height[i] >= 0, height[i] < n))
        s.add(And(cigar[i] >= 0, cigar[i] < n))
    
    # Distinct constraints
    s.add(Distinct(name))
    s.add(Distinct(house_style))
    s.add(Distinct(food))
    s.add(Distinct(vacation))
    s.add(Distinct(height))
    s.add(Distinct(cigar))
    
    # Clue 1: Alice is in the fifth house
    s.add(name[4] == Alice)
    
    # Clue 2: Stir fry eater is in colonial house (equivalence)
    s.add(And([(food[i] == stir_fry) == (house_style[i] == colonial) for i in range(n)]))
    
    # Clue 3: Alice eats spaghetti
    s.add(food[4] == spaghetti)
    
    # Clue 4: Arnold eats stew (equivalence)
    s.add(And([(name[i] == Arnold) == (food[i] == stew) for i in range(n)]))
    
    # Clue 5: One house between average height and Peter
    s.add(Or(
        [And(height[i] == average, name[i+2] == Peter) for i in range(n-2)] +
        [And(height[i] == average, name[i-2] == Peter) for i in range(2, n)]
    ))
    
    # Clue 6: Craftsman not in third house
    s.add(house_style[2] != craftsman)
    
    # Clue 7: Average height is stir fry eater (equivalence)
    s.add(And([(height[i] == average) == (food[i] == stir_fry) for i in range(n)]))
    
    # Clue 8: Beach vacation is in ranch house (equivalence)
    s.add(And([(vacation[i] == beach) == (house_style[i] == ranch) for i in range(n)]))
    
    # Clue 9: Eric in fourth house
    s.add(name[3] == Eric)
    
    # Clue 10: One house between colonial and camping
    s.add(Or(
        [And(house_style[i] == colonial, vacation[i+2] == camping) for i in range(n-2)] +
        [And(house_style[i] == colonial, vacation[i-2] == camping) for i in range(2, n)]
    ))
    
    # Clue 11: Mountain vacation smokes Yellow Monster (equivalence)
    s.add(And([(vacation[i] == mountain) == (cigar[i] == yellow_monster) for i in range(n)]))
    
    # Clue 12: Mountain vacation is very tall (equivalence)
    s.add(And([(vacation[i] == mountain) == (height[i] == very_tall) for i in range(n)]))
    
    # Clue 13: Mountain and Dunhill smoker are adjacent
    s.add(Or(
        [And(vacation[i] == mountain, cigar[i+1] == dunhill) for i in range(n-1)] +
        [And(vacation[i] == mountain, cigar[i-1] == dunhill) for i in range(1, n)]
    ))
    
    # Clue 14: Spaghetti eater is in Victorian house
    s.add(house_style[4] == victorian)
    
    # Clue 15: Tall height is beach vacation (equivalence)
    s.add(And([(height[i] == tall) == (vacation[i] == beach) for i in range(n)]))
    
    # Clue 16: Tall is left of Victorian
    tall_idx = Sum([If(height[i] == tall, i, 0) for i in range(n)])
    victorian_idx = Sum([If(house_style[i] == victorian, i, 0) for i in range(n)])
    s.add(tall_idx < victorian_idx)
    
    # Clue 17: Stir fry is directly left of Bob
    s.add(Or([And(food[i] == stir_fry, name[i+1] == Bob) for i in range(n-1)]))
    
    # Clue 18: Modern style is left of Alice (house index < 4)
    modern_idx = Sum([If(house_style[i] == modern, i, 0) for i in range(n)])
    s.add(modern_idx < 4)
    
    # Clue 19: Craftsman is left of short height
    craftsman_idx = Sum([If(house_style[i] == craftsman, i, 0) for i in range(n)])
    short_idx = Sum([If(height[i] == short, i, 0) for i in range(n)])
    s.add(craftsman_idx < short_idx)
    
    # Clue 20: Stir fry is left of Prince smoker
    stir_fry_idx = Sum([If(food[i] == stir_fry, i, 0) for i in range(n)])
    prince_idx = Sum([If(cigar[i] == prince, i, 0) for i in range(n)])
    s.add(stir_fry_idx < prince_idx)
    
    # Clue 21: Two houses between grilled cheese and super tall
    s.add(Or(
        [And(food[i] == grilled_cheese, height[i+3] == super_tall) for i in range(n-3)] +
        [And(food[i] == grilled_cheese, height[i-3] == super_tall) for i in range(3, n)]
    ))
    
    # Clue 22: Ranch house smokes Blue Master (equivalence)
    s.add(And([(house_style[i] == ranch) == (cigar[i] == blue_master) for i in range(n)]))
    
    # Clue 23: Blends smoker is directly left of Blue Master smoker
    s.add(Or([And(cigar[i] == blends, cigar[i+1] == blue_master) for i in range(n-1)]))
    
    # Clue 24: Cultural vacation is pizza eater (equivalence)
    s.add(And([(vacation[i] == cultural) == (food[i] == pizza) for i in range(n)]))
    
    # Clue 25: Pizza eater is left of cruise vacation
    pizza_idx = Sum([If(food[i] == pizza, i, 0) for i in range(n)])
    cruise_idx = Sum([If(vacation[i] == cruise, i, 0) for i in range(n)])
    s.add(pizza_idx < cruise_idx)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        solution = []
        for i in range(n):
            n_val = m.evaluate(name[i]).as_long()
            hs_val = m.evaluate(house_style[i]).as_long()
            f_val = m.evaluate(food[i]).as_long()
            v_val = m.evaluate(vacation[i]).as_long()
            h_val = m.evaluate(height[i]).as_long()
            c_val = m.evaluate(cigar[i]).as_long()
            solution.append([
                str(i+1),
                names[n_val],
                house_styles[hs_val],
                foods[f_val],
                vacations[v_val],
                heights[h_val],
                cigars[c_val]
            ])
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": solution
            }
        }
        print(json.dumps(output))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()