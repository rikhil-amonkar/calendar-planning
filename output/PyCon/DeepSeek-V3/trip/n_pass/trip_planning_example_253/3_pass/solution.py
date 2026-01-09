import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their durations
    cities = {
        'Amsterdam': 3,
        'Vienna': 7, 
        'Santorini': 4,
        'Lyon': 3
    }
    
    # Total days available
    total_days = 14
    
    # Flight connections (direct flights only)
    connections = {
        'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
        'Lyon': ['Vienna', 'Amsterdam'],
        'Santorini': ['Vienna', 'Amsterdam'],
        'Amsterdam': ['Vienna', 'Santorini', 'Lyon']
    }
    
    # Define visit order for each city (0-3)
    for city in cities:
        problem.addVariable(f'order_{city}', range(4))
    
    # All cities must have different visit orders
    problem.addConstraint(AllDifferentConstraint(), [f'order_{city}' for city in cities])
    
    def itinerary_valid(order_amsterdam, order_vienna, order_santorini, order_lyon):
        # Create visit sequence
        visit_sequence = [
            (order_amsterdam, 'Amsterdam'),
            (order_vienna, 'Vienna'),
            (order_santorini, 'Santorini'), 
            (order_lyon, 'Lyon')
        ]
        visit_sequence.sort()
        
        # Check flight connections between consecutive cities
        for i in range(len(visit_sequence) - 1):
            current_city = visit_sequence[i][1]
            next_city = visit_sequence[i + 1][1]
            if next_city not in connections[current_city]:
                return False
        
        # Calculate day ranges
        current_day = 1
        amsterdam_days = []
        lyon_days = []
        
        for order, city in visit_sequence:
            duration = cities[city]
            start_day = current_day
            end_day = current_day + duration - 1
            
            if city == 'Amsterdam':
                amsterdam_days = list(range(start_day, end_day + 1))
            elif city == 'Lyon':
                lyon_days = list(range(start_day, end_day + 1))
            
            current_day = end_day + 1
        
        # Check if total days doesn't exceed 14
        if current_day - 1 > total_days:
            return False
        
        # Check workshop constraint: Amsterdam must include at least one day between 9-11
        workshop_valid = any(day in amsterdam_days for day in [9, 10, 11])
        if not workshop_valid:
            return False
        
        # Check wedding constraint: Lyon must include at least one day between 7-9
        wedding_valid = any(day in lyon_days for day in [7, 8, 9])
        if not wedding_valid:
            return False
        
        return True
    
    # Add the main constraint
    problem.addConstraint(itinerary_valid, 
                         ['order_Amsterdam', 'order_Vienna', 'order_Santorini', 'order_Lyon'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try a more systematic approach
        return find_valid_itinerary_manually()
    
    # Use first solution
    sol = solutions[0]
    
    # Build the itinerary
    visit_info = [
        (sol['order_Amsterdam'], 'Amsterdam'),
        (sol['order_Vienna'], 'Vienna'),
        (sol['order_Santorini'], 'Santorini'),
        (sol['order_Lyon'], 'Lyon')
    ]
    visit_info.sort()
    
    itinerary = []
    current_day = 1
    
    for _, city in visit_info:
        duration = cities[city]
        end_day = current_day + duration - 1
        
        if current_day == end_day:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    return {"itinerary": itinerary}

def find_valid_itinerary_manually():
    """Find a valid itinerary by systematically checking possibilities"""
    cities = {
        'Amsterdam': 3,
        'Vienna': 7, 
        'Santorini': 4,
        'Lyon': 3
    }
    
    connections = {
        'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
        'Lyon': ['Vienna', 'Amsterdam'],
        'Santorini': ['Vienna', 'Amsterdam'],
        'Amsterdam': ['Vienna', 'Santorini', 'Lyon']
    }
    
    # Try different visit orders
    from itertools import permutations
    city_names = list(cities.keys())
    
    for visit_order in permutations(city_names):
        # Check flight connections
        valid_connections = True
        for i in range(len(visit_order) - 1):
            if visit_order[i+1] not in connections[visit_order[i]]:
                valid_connections = False
                break
        
        if not valid_connections:
            continue
            
        # Calculate day ranges
        current_day = 1
        amsterdam_days = []
        lyon_days = []
        
        for city in visit_order:
            duration = cities[city]
            start_day = current_day
            end_day = current_day + duration - 1
            
            if city == 'Amsterdam':
                amsterdam_days = list(range(start_day, end_day + 1))
            elif city == 'Lyon':
                lyon_days = list(range(start_day, end_day + 1))
            
            current_day = end_day + 1
        
        # Check total days
        if current_day - 1 > 14:
            continue
            
        # Check workshop constraint (Amsterdam days 9-11)
        workshop_valid = any(day in amsterdam_days for day in [9, 10, 11])
        if not workshop_valid:
            continue
            
        # Check wedding constraint (Lyon days 7-9)
        wedding_valid = any(day in lyon_days for day in [7, 8, 9])
        if not wedding_valid:
            continue
        
        # Found valid itinerary
        itinerary = []
        current_day = 1
        
        for city in visit_order:
            duration = cities[city]
            end_day = current_day + duration - 1
            
            if current_day == end_day:
                day_range = f"Day {current_day}"
            else:
                day_range = f"Day {current_day}-{end_day}"
            
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
            
            current_day = end_day + 1
        
        return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))