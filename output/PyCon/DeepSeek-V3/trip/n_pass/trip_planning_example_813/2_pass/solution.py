import constraint
import json
from itertools import permutations

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    # Direct flight connections (bidirectional)
    flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    # Total days
    total_days = 17
    
    # Special constraints
    london_meet_days = [9, 10]  # Must be in London on day 9 and 10
    stuttgart_relatives_days = [7, 8, 9]  # Must be in Stuttgart on day 7, 8, and 9
    
    # We'll model this as finding a permutation of cities that satisfies constraints
    city_names = list(cities.keys())
    
    # Add variables for the order
    for i in range(len(city_names)):
        problem.addVariable(f'city_{i}', city_names)
    
    # Constraint: all cities must be different (permutation)
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'city_{i}' for i in range(len(city_names))])
    
    # Constraint: consecutive cities must have flight connections
    for i in range(len(city_names) - 1):
        problem.addConstraint(
            lambda city1, city2: city2 in flights.get(city1, []),
            [f'city_{i}', f'city_{i+1}']
        )
    
    # Find valid permutations
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"itinerary": [], "error": "No valid city sequence found"}
        print(json.dumps(result))
        return
    
    # For each valid permutation, check if we can schedule days that satisfy constraints
    valid_itineraries = []
    
    for solution in solutions:
        # Get the city order from the solution
        city_order = [solution[f'city_{i}'] for i in range(len(city_names))]
        
        # Calculate total days needed (including travel days)
        total_needed = sum(cities[city] for city in city_order)
        
        if total_needed > total_days:
            continue
            
        # Try to find start days that satisfy all constraints
        start_days = [1]  # Start with first city on day 1
        
        for i in range(1, len(city_order)):
            prev_city = city_order[i-1]
            current_city = city_order[i]
            start_days.append(start_days[i-1] + cities[prev_city])
        
        # Check if this schedule fits within total days
        last_city_end = start_days[-1] + cities[city_order[-1]] - 1
        if last_city_end > total_days:
            continue
        
        # Check London constraint (must cover days 9 and 10)
        london_satisfied = False
        for i, city in enumerate(city_order):
            if city == 'London':
                london_start = start_days[i]
                london_end = london_start + cities['London'] - 1
                if london_start <= 9 and london_end >= 10:
                    london_satisfied = True
                    break
        
        if not london_satisfied:
            continue
        
        # Check Stuttgart constraint (must cover days 7, 8, and 9)
        stuttgart_satisfied = False
        for i, city in enumerate(city_order):
            if city == 'Stuttgart':
                stuttgart_start = start_days[i]
                stuttgart_end = stuttgart_start + cities['Stuttgart'] - 1
                if stuttgart_start <= 7 and stuttgart_end >= 9:
                    stuttgart_satisfied = True
                    break
        
        if not stuttgart_satisfied:
            continue
        
        # If we get here, we have a valid itinerary
        itinerary = []
        for i, city in enumerate(city_order):
            start = start_days[i]
            end = start + cities[city] - 1
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        valid_itineraries.append(itinerary)
        break  # Just take the first valid one
    
    if valid_itineraries:
        result = {"itinerary": valid_itineraries[0]}
        print(json.dumps(result, indent=2))
    else:
        result = {"itinerary": [], "error": "No valid itinerary found that satisfies all constraints"}
        print(json.dumps(result))

if __name__ == "__main__":
    main()