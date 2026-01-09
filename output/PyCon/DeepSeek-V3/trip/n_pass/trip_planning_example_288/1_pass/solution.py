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
    stuttgart_workshop_start = 11
    stuttgart_workshop_end = 15
    manchester_wedding_start = 1
    manchester_wedding_end = 7
    
    # Direct flight connections
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    # We need to model the itinerary as a sequence of stays
    # Each stay has: start_day, end_day, city
    # Since we have 4 cities and need to visit all, we'll model the order
    
    # Variables: order of cities and durations
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    
    # Add variables for the order
    for i in range(len(cities)):
        problem.addVariable(f'city_{i}', cities)
    
    # Add variables for start days (except first city which starts at day 1)
    problem.addVariable('start_1', range(2, total_days))
    problem.addVariable('start_2', range(2, total_days))
    problem.addVariable('start_3', range(2, total_days))
    
    # All cities must be different in the order
    problem.addConstraint(constraint.AllDifferentConstraint(), ['city_0', 'city_1', 'city_2', 'city_3'])
    
    def itinerary_constraint(city_0, city_1, city_2, city_3, start_1, start_2, start_3):
        # Build the itinerary
        itinerary = [
            {'city': city_0, 'start': 1, 'end': start_1 - 1},
            {'city': city_1, 'start': start_1, 'end': start_2 - 1},
            {'city': city_2, 'start': start_2, 'end': start_3 - 1},
            {'city': city_3, 'start': start_3, 'end': total_days}
        ]
        
        # Check total days per city
        city_days = {'Manchester': 0, 'Stuttgart': 0, 'Madrid': 0, 'Vienna': 0}
        for stay in itinerary:
            days = stay['end'] - stay['start'] + 1
            city_days[stay['city']] += days
        
        # Check required days
        if (city_days['Manchester'] != manchester_days or
            city_days['Stuttgart'] != stuttgart_days or
            city_days['Madrid'] != madrid_days or
            city_days['Vienna'] != vienna_days):
            return False
        
        # Check workshop and wedding constraints
        for stay in itinerary:
            city = stay['city']
            start = stay['start']
            end = stay['end']
            
            if city == 'Stuttgart':
                # Must include workshop days (11-15)
                if not (start <= stuttgart_workshop_start and end >= stuttgart_workshop_end):
                    return False
            
            if city == 'Manchester':
                # Must include wedding days (1-7)
                if not (start <= manchester_wedding_start and end >= manchester_wedding_end):
                    return False
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if next_city not in direct_flights[current_city]:
                return False
        
        # Check day ordering
        if not (1 < start_1 < start_2 < start_3 <= total_days):
            return False
            
        # Check no negative durations
        for stay in itinerary:
            if stay['end'] < stay['start']:
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
    
    # Build the itinerary
    itinerary = [
        {'city': sol['city_0'], 'start': 1, 'end': sol['start_1'] - 1},
        {'city': sol['city_1'], 'start': sol['start_1'], 'end': sol['start_2'] - 1},
        {'city': sol['city_2'], 'start': sol['start_2'], 'end': sol['start_3'] - 1},
        {'city': sol['city_3'], 'start': sol['start_3'], 'end': total_days}
    ]
    
    # Format output
    output_itinerary = []
    for stay in itinerary:
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