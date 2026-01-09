import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 
              'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    
    # Define variables for arrival day for each city (1-29)
    for city in cities:
        problem.addVariable(f'arrive_{city}', range(1, 30))
    
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
    
    # Event constraints - CORRECTED
    # The entire stay must be within the event window
    def athens_workshop_constraint(arrive_athens):
        duration = stay_durations['Athens']
        return 14 <= arrive_athens <= 29 - duration + 1 and arrive_athens + duration - 1 <= 18
    
    def valencia_show_constraint(arrive_valencia):
        duration = stay_durations['Valencia']
        return 5 <= arrive_valencia <= 29 - duration + 1 and arrive_valencia + duration - 1 <= 6
    
    def vienna_wedding_constraint(arrive_vienna):
        duration = stay_durations['Vienna']
        return 6 <= arrive_vienna <= 29 - duration + 1 and arrive_vienna + duration - 1 <= 10
    
    def stockholm_friend_constraint(arrive_stockholm):
        duration = stay_durations['Stockholm']
        return 1 <= arrive_stockholm <= 3 - duration + 1
    
    def riga_conference_constraint(arrive_riga):
        duration = stay_durations['Riga']
        return 18 <= arrive_riga <= 29 - duration + 1 and arrive_riga + duration - 1 <= 20
    
    problem.addConstraint(athens_workshop_constraint, ['arrive_Athens'])
    problem.addConstraint(valencia_show_constraint, ['arrive_Valencia'])
    problem.addConstraint(vienna_wedding_constraint, ['arrive_Vienna'])
    problem.addConstraint(stockholm_friend_constraint, ['arrive_Stockholm'])
    problem.addConstraint(riga_conference_constraint, ['arrive_Riga'])
    
    # All arrival days must be different
    problem.addConstraint(AllDifferentConstraint(), [f'arrive_{city}' for city in cities])
    
    # Flight connections (bidirectional)
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
    
    # Make connections bidirectional
    bidirectional_connections = set()
    for conn in connections:
        bidirectional_connections.add(conn)
        bidirectional_connections.add((conn[1], conn[0]))
    
    # Simplified itinerary constraint - just check total duration
    def total_duration_constraint(*arrivals):
        arrival_dict = {}
        for i, city in enumerate(cities):
            arrival_dict[city] = arrivals[i]
        
        # Find earliest arrival and latest departure
        earliest_arrival = min(arrival_dict.values())
        latest_departure = max(arrival_dict[city] + stay_durations[city] - 1 for city in cities)
        
        total_duration = latest_departure - earliest_arrival + 1
        
        # Total trip should be exactly 29 days
        return total_duration == 29
    
    problem.addConstraint(total_duration_constraint, [f'arrive_{city}' for city in cities])
    
    # Additional constraint: consecutive cities must be connected
    def consecutive_cities_connected(*arrivals):
        arrival_dict = {}
        for i, city in enumerate(cities):
            arrival_dict[city] = arrivals[i]
        
        # Create list of (arrival, city) pairs and sort by arrival
        city_arrivals = [(arrival_dict[city], city) for city in cities]
        city_arrivals.sort()
        
        # Check consecutive cities for flight connections
        for i in range(len(city_arrivals) - 1):
            current_city = city_arrivals[i][1]
            next_city = city_arrivals[i + 1][1]
            
            if (current_city, next_city) not in bidirectional_connections:
                return False
        
        return True
    
    problem.addConstraint(consecutive_cities_connected, [f'arrive_{city}' for city in cities])
    
    # Additional constraint: no overlapping stays
    def no_overlapping_stays(*arrivals):
        arrival_dict = {}
        for i, city in enumerate(cities):
            arrival_dict[city] = arrivals[i]
        
        # Check each pair of cities for overlap
        for i, city1 in enumerate(cities):
            for j, city2 in enumerate(cities):
                if i < j:  # Avoid duplicate checks
                    start1 = arrival_dict[city1]
                    end1 = start1 + stay_durations[city1] - 1
                    start2 = arrival_dict[city2]
                    end2 = start2 + stay_durations[city2] - 1
                    
                    # Check if stays overlap
                    if not (end1 < start2 or end2 < start1):
                        return False
        
        return True
    
    problem.addConstraint(no_overlapping_stays, [f'arrive_{city}' for city in cities])
    
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