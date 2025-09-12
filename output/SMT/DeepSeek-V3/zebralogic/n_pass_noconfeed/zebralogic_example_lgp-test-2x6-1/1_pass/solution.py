import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Arnold', 'Eric']
    sports = ['basketball', 'soccer']
    hair_colors = ['brown', 'black']
    heights = ['very short', 'short']
    smoothies = ['desert', 'cherry']
    flowers = ['daffodils', 'carnations']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    sport_vars = {h: z3.Int(f'sport_{h}') for h in houses}
    hair_vars = {h: z3.Int(f'hair_{h}') for h in houses}
    height_vars = {h: z3.Int(f'height_{h}') for h in houses}
    smoothie_vars = {h: z3.Int(f'smoothie_{h}') for h in houses}
    flower_vars = {h: z3.Int(f'flower_{h}') for h in houses}
    
    # Define domain constraints for each attribute
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(sport_vars[h] >= 0, sport_vars[h] < len(sports)))
        solver.add(z3.And(hair_vars[h] >= 0, hair_vars[h] < len(hair_colors)))
        solver.add(z3.And(height_vars[h] >= 0, height_vars[h] < len(heights)))
        solver.add(z3.And(smoothie_vars[h] >= 0, smoothie_vars[h] < len(smoothies)))
        solver.add(z3.And(flower_vars[h] >= 0, flower_vars[h] < len(flowers)))
    
    # All attributes must be distinct within their category
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    solver.add(z3.Distinct([sport_vars[h] for h in houses]))
    solver.add(z3.Distinct([hair_vars[h] for h in houses]))
    solver.add(z3.Distinct([height_vars[h] for h in houses]))
    solver.add(z3.Distinct([smoothie_vars[h] for h in houses]))
    solver.add(z3.Distinct([flower_vars[h] for h in houses]))
    
    # Clue 1: The person who loves soccer is not in the second house.
    soccer_index = sports.index('soccer')
    solver.add(sport_vars[2] != soccer_index)
    
    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    desert_index = smoothies.index('desert')
    very_short_index = heights.index('very short')
    solver.add(smoothie_vars[1] == desert_index)
    solver.add(height_vars[2] == very_short_index)
    
    # Clue 3: The person who is very short is the person who has brown hair.
    brown_hair_index = hair_colors.index('brown')
    solver.add(hair_vars[2] == brown_hair_index)  # very short is in house 2
    
    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    carnations_index = flowers.index('carnations')
    solver.add(flower_vars[1] == carnations_index)  # desert smoothie is in house 1
    
    # Clue 5: Eric and the person who has brown hair are next to each other.
    eric_index = names.index('Eric')
    # Brown hair is in house 2, so Eric must be in adjacent house (house 1)
    solver.add(name_vars[1] == eric_index)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in sorted(houses):
            name_val = names[model.evaluate(name_vars[house]).as_long()]
            sport_val = sports[model.evaluate(sport_vars[house]).as_long()]
            hair_val = hair_colors[model.evaluate(hair_vars[house]).as_long()]
            height_val = heights[model.evaluate(height_vars[house]).as_long()]
            smoothie_val = smoothies[model.evaluate(smoothie_vars[house]).as_long()]
            flower_val = flowers[model.evaluate(flower_vars[house]).as_long()]
            
            result["solution"]["rows"].append([
                str(house),
                name_val,
                sport_val,
                hair_val,
                height_val,
                smoothie_val,
                flower_val
            ])
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()