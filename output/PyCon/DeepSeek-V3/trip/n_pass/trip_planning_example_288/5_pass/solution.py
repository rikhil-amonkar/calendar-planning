import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Total days
    total_days = 15
    
    # City requirements
    stuttgart_days = 5
    manchester_days = 7
    madrid_days = 4
    vienna_days = 2
    
    # Workshop and wedding constraints
    stuttgart_workshop_days = [11, 12, 13, 14, 15]  # Days 11-15
    manchester_wedding_days = [1, 2, 3, 4, 5, 6, 7]  # Days 1-7
    
    # Direct flight connections
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    # We'll use a more flexible approach with 4 stays (which could include multiple visits to the same city)
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    
    # Add variables for the cities in each stay
    for i in range(4):
        problem.addVariable(f'city_{i}', cities)
    
    # Add variables for start days (more flexible ranges)
    problem.addVariable('start_1', range(2, total_days - 5))
    problem.addVariable('start_2', range(3, total_days - 3))
    problem.addVariable('start_3', range(4, total_days - 1))
    
    def itinerary_constraint(city_0, city_1, city_2, city_3, start_1, start_2, start_3):
        # Build the itinerary
        itinerary = [
            {'city': city_0, 'start': 1, 'end': start_1 - 1},
            {'city': city_1, 'start': start_1, 'end': start_2 - 1},
            {'city': city_2, 'start': start_2, 'end': start_3 - 1},
            {'city': city_3, 'start': start_3, 'end': total_days}
        ]
        
        # Check day ordering
        if not (1 < start_1 < start_2 < start_3 <= total_days):
            return False
        
        # Check that each stay has at least 1 day
        for stay in itinerary:
            if stay['end'] < stay['start']:
                return False
        
        # Check total days per city
        city_days = {'Manchester': 0, 'Stuttgart': 0, 'Madrid': 0, 'Vienna': 0}
        for stay in itinerary:
            days = stay['end'] - stay['start'] + 1
            if days <= 0:
                return False
            city_days[stay['city']] += days
        
        # Check required days
        if (city_days['Manchester'] != manchester_days or
            city_days['Stuttgart'] != stuttgart_days or
            city_days['Madrid'] != madrid_days or
            city_days['Vienna'] != vienna_days):
            return False
        
        # Check workshop and wedding constraints
        manchester_visit_days = []
        stuttgart_visit_days = []
        
        for stay in itinerary:
            city = stay['city']
            start = stay['start']
            end = stay['end']
            
            if city == 'Manchester':
                manchester_visit_days.extend(range(start, end + 1))
            elif city == 'Stuttgart':
                stuttgart_visit_days.extend(range(start, end + 1))
        
        # Check if Manchester visit includes all wedding days (1-7)
        if not all(day in manchester_visit_days for day in manchester_wedding_days):
            return False
        
        # Check if Stuttgart visit includes all workshop days (11-15)
        if not all(day in stuttgart_visit_days for day in stuttgart_workshop_days):
            return False
        
        # Check flight connections between consecutive cities
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if current_city != next_city:  # Only check flights between different cities
                if next_city not in direct_flights[current_city]:
                    return False
        
        return True
    
    problem.addConstraint(
        itinerary_constraint, 
        ['city_0', 'city_1', 'city_2', 'city_3', 'start_1', 'start_2', 'start_3']
    )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Take the first solution
    sol = solutions[0]
    
    # Build the itinerary and merge consecutive stays in the same city
    raw_itinerary = [
        {'city': sol['city_0'], 'start': 1, 'end': sol['start_1'] - 1},
        {'city': sol['city_1'], 'start': sol['start_1'], 'end': sol['start_2'] - 1},
        {'city': sol['city_2'], 'start': sol['start_2'], 'end': sol['start_3'] - 1},
        {'city': sol['city_3'], 'start': sol['start_3'], 'end': total_days}
    ]
    
    # Merge consecutive stays in the same city
    merged_itinerary = []
    current_stay = raw_itinerary[0]
    
    for i in range(1, len(raw_itinerary)):
        if raw_itinerary[i]['city'] == current_stay['city']:
            # Extend the current stay
            current_stay['end'] = raw_itinerary[i]['end']
        else:
            # Add the current stay and start a new one
            merged_itinerary.append(current_stay)
            current_stay = raw_itinerary[i]
    
    merged_itinerary.append(current_stay)
    
    # Format output
    output_itinerary = []
    for stay in merged_itinerary:
        if stay['start'] == stay['end']:
            day_range = f"Day {stay['start']}"
        else:
            day_range = f"Day {stay['start']}-{stay['end']}"
        output_itinerary.append({
            "day_range": day_range,
            "place": stay['city']
        })
    
    result = {"itinerary": output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()