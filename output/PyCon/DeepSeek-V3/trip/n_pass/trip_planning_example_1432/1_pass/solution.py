import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 
              'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    
    # Define variables for arrival day for each city
    for city in cities:
        problem.addVariable(f'arrive_{city}', range(1, 30))
    
    # Total days constraint
    total_days = 29
    
    # Fixed stay durations
    stay_durations = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    # Event constraints
    def athens_workshop_constraint(arrive_athens):
        return 14 <= arrive_athens <= 18 - stay_durations['Athens'] + 1
    
    def valencia_show_constraint(arrive_valencia):
        return 5 <= arrive_valencia <= 6 - stay_durations['Valencia'] + 1
    
    def vienna_wedding_constraint(arrive_vienna):
        return 6 <= arrive_vienna <= 10 - stay_durations['Vienna'] + 1
    
    def stockholm_friend_constraint(arrive_stockholm):
        return 1 <= arrive_stockholm <= 3 - stay_durations['Stockholm'] + 1
    
    def riga_conference_constraint(arrive_riga):
        return 18 <= arrive_riga <= 20 - stay_durations['Riga'] + 1
    
    problem.addConstraint(athens_workshop_constraint, ['arrive_Athens'])
    problem.addConstraint(valencia_show_constraint, ['arrive_Valencia'])
    problem.addConstraint(vienna_wedding_constraint, ['arrive_Vienna'])
    problem.addConstraint(stockholm_friend_constraint, ['arrive_Stockholm'])
    problem.addConstraint(riga_conference_constraint, ['arrive_Riga'])
    
    # Flight connections
    connections = [
        ('Valencia', 'Frankfurt'), ('Vienna', 'Bucharest'), ('Valencia', 'Athens'),
        ('Athens', 'Bucharest'), ('Riga', 'Frankfurt'), ('Stockholm', 'Athens'),
        ('Amsterdam', 'Bucharest'), ('Athens', 'Riga'), ('Amsterdam', 'Frankfurt'),
        ('Stockholm', 'Vienna'), ('Vienna', 'Riga'), ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Frankfurt'), ('Stockholm', 'Amsterdam'), ('Amsterdam', 'Valencia'),
        ('Vienna', 'Frankfurt'), ('Valencia', 'Bucharest'), ('Bucharest', 'Frankfurt'),
        ('Stockholm', 'Frankfurt'), ('Valencia', 'Vienna'), ('Reykjavik', 'Athens'),
        ('Frankfurt', 'Salzburg'), ('Amsterdam', 'Vienna'), ('Stockholm', 'Reykjavik'),
        ('Amsterdam', 'Riga'), ('Stockholm', 'Riga'), ('Vienna', 'Reykjavik'),
        ('Amsterdam', 'Athens'), ('Athens', 'Frankfurt'), ('Vienna', 'Athens'),
        ('Riga', 'Bucharest')
    ]
    
    # Ensure cities are visited in sequence with valid flights
    def valid_itinerary(*arrivals):
        arrival_dict = {}
        for i, city in enumerate(cities):
            arrival_dict[city] = arrivals[i]
        
        # Sort cities by arrival day
        visit_order = sorted(cities, key=lambda x: arrival_dict[x])
        
        # Check if consecutive cities are connected by flights
        for i in range(len(visit_order) - 1):
            city1 = visit_order[i]
            city2 = visit_order[i + 1]
            
            # Check if there's a direct flight between consecutive cities
            if (city1, city2) not in connections and (city2, city1) not in connections:
                return False
            
            # Check if departure from city1 happens after stay duration
            depart_city1 = arrival_dict[city1] + stay_durations[city1] - 1
            arrive_city2 = arrival_dict[city2]
            
            if arrive_city2 <= depart_city1:
                return False
        
        # Check total days
        last_city = visit_order[-1]
        total_trip_days = arrival_dict[last_city] + stay_durations[last_city] - 1
        if total_trip_days != total_days:
            return False
        
        return True
    
    problem.addConstraint(valid_itinerary, [f'arrive_{city}' for city in cities])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = solutions[0]
    
    # Create itinerary
    itinerary = []
    city_stays = []
    
    for city in cities:
        arrival = solution[f'arrive_{city}']
        duration = stay_durations[city]
        departure = arrival + duration - 1
        city_stays.append((arrival, departure, city))
    
    # Sort by arrival day
    city_stays.sort()
    
    # Build final itinerary
    for arrival, departure, city in city_stays:
        if arrival == departure:
            day_range = f"Day {arrival}"
        else:
            day_range = f"Day {arrival}-{departure}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output result
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()