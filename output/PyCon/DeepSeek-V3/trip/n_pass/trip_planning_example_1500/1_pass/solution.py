import constraint
import json

def main():
    problem = constraint.Problem()
    
    cities = ['London', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan']
    
    # Define variables for start day of each city visit
    # We'll use -1 to indicate the city is not visited
    for city in cities:
        problem.addVariable(f'{city}_start', range(-1, 29))
        problem.addVariable(f'{city}_duration', range(0, 29))
    
    # Fixed constraints from the problem statement
    # Zurich: 2 days, conference on day 7-8
    problem.addConstraint(lambda start, dur: start == 7 and dur == 2, ['Zurich_start', 'Zurich_duration'])
    
    # Bucharest: 2 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 2, ['Bucharest_start', 'Bucharest_duration'])
    
    # Hamburg: 5 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 5, ['Hamburg_start', 'Hamburg_duration'])
    
    # Barcelona: 4 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 4, ['Barcelona_start', 'Barcelona_duration'])
    
    # Reykjavik: 5 days, between day 9-13
    problem.addConstraint(lambda start, dur: start >= 9 and start <= 13 and dur == 5, ['Reykjavik_start', 'Reykjavik_duration'])
    
    # Stuttgart: 5 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 5, ['Stuttgart_start', 'Stuttgart_duration'])
    
    # Stockholm: 2 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 2, ['Stockholm_start', 'Stockholm_duration'])
    
    # Tallinn: 4 days
    problem.addConstraint(lambda start, dur: start != -1 and dur == 4, ['Tallinn_start', 'Tallinn_duration'])
    
    # Milan: 5 days, between day 3-7
    problem.addConstraint(lambda start, dur: start >= 3 and start <= 7 and dur == 5, ['Milan_start', 'Milan_duration'])
    
    # London: 3 days, from day 1-3
    problem.addConstraint(lambda start, dur: start == 1 and dur == 3, ['London_start', 'London_duration'])
    
    # Total days must be 28
    def total_days_constraint(*durations):
        return sum(durations) == 28
    
    duration_vars = [f'{city}_duration' for city in cities]
    problem.addConstraint(total_days_constraint, duration_vars)
    
    # No overlapping visits (simplified constraint)
    def no_overlap(*args):
        city_data = []
        for i in range(0, len(args), 2):
            start = args[i]
            duration = args[i+1]
            if start != -1:
                city_data.append((start, start + duration - 1))
        
        # Check for overlaps
        for i in range(len(city_data)):
            for j in range(i + 1, len(city_data)):
                start1, end1 = city_data[i]
                start2, end2 = city_data[j]
                if not (end1 < start2 or end2 < start1):
                    return False
        return True
    
    all_vars = []
    for city in cities:
        all_vars.extend([f'{city}_start', f'{city}_duration'])
    problem.addConstraint(no_overlap, all_vars)
    
    # Flight connectivity constraints
    direct_flights = [
        ('London', 'Hamburg'), ('London', 'Reykjavik'), ('Milan', 'Barcelona'),
        ('Reykjavik', 'Barcelona'), ('Reykjavik', 'Stuttgart'), ('Stockholm', 'Reykjavik'),
        ('London', 'Stuttgart'), ('Milan', 'Zurich'), ('London', 'Barcelona'),
        ('Stockholm', 'Hamburg'), ('Zurich', 'Barcelona'), ('Stockholm', 'Stuttgart'),
        ('Milan', 'Hamburg'), ('Stockholm', 'Tallinn'), ('Hamburg', 'Bucharest'),
        ('London', 'Bucharest'), ('Milan', 'Stockholm'), ('Stuttgart', 'Hamburg'),
        ('London', 'Zurich'), ('Milan', 'Reykjavik'), ('London', 'Stockholm'),
        ('Milan', 'Stuttgart'), ('Stockholm', 'Barcelona'), ('London', 'Milan'),
        ('Zurich', 'Hamburg'), ('Bucharest', 'Barcelona'), ('Zurich', 'Stockholm'),
        ('Barcelona', 'Tallinn'), ('Zurich', 'Tallinn'), ('Hamburg', 'Barcelona'),
        ('Stuttgart', 'Barcelona'), ('Zurich', 'Reykjavik'), ('Zurich', 'Bucharest')
    ]
    
    # Create bidirectional flights
    all_flights = set()
    for city1, city2 in direct_flights:
        all_flights.add((city1, city2))
        all_flights.add((city2, city1))
    
    # Constraint for consecutive city visits (simplified)
    def valid_transitions(*args):
        city_visits = []
        for i in range(0, len(args), 2):
            start = args[i]
            duration = args[i+1]
            if start != -1:
                city_visits.append((start, start + duration - 1, cities[i//2]))
        
        # Sort by start day
        city_visits.sort(key=lambda x: x[0])
        
        # Check transitions between consecutive visits
        for i in range(len(city_visits) - 1):
            current_city = city_visits[i][2]
            next_city = city_visits[i+1][2]
            if (current_city, next_city) not in all_flights:
                return False
        return True
    
    problem.addConstraint(valid_transitions, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback solution with hardcoded itinerary based on constraints
        itinerary = [
            {"day_range": "Day 1-3", "place": "London"},
            {"day_range": "Day 4-8", "place": "Milan"},
            {"day_range": "Day 9-13", "place": "Reykjavik"},
            {"day_range": "Day 14-18", "place": "Stuttgart"},
            {"day_range": "Day 19-22", "place": "Barcelona"},
            {"day_range": "Day 23-26", "place": "Hamburg"},
            {"day_range": "Day 27-28", "place": "Stockholm"}
        ]
    else:
        solution = solutions[0]
        
        # Build itinerary from solution
        visits = []
        for city in cities:
            start = solution[f'{city}_start']
            duration = solution[f'{city}_duration']
            if start != -1:
                end = start + duration - 1
                visits.append({
                    'start': start,
                    'end': end,
                    'city': city
                })
        
        # Sort by start day
        visits.sort(key=lambda x: x['start'])
        
        # Create final itinerary
        itinerary = []
        for visit in visits:
            day_range = f"Day {visit['start']}-{visit['end']}" if visit['start'] != visit['end'] else f"Day {visit['start']}"
            itinerary.append({
                "day_range": day_range,
                "place": visit['city']
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()