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
    
    # Event constraints - FIXED
    # These should ensure the entire stay falls within the event window
    def athens_workshop_constraint(arrive_athens):
        duration = stay_durations['Athens']
        return 14 <= arrive_athens <= 18 - duration + 1
    
    def valencia_show_constraint(arrive_valencia):
        duration = stay_durations['Valencia']
        return 5 <= arrive_valencia <= 6 - duration + 1
    
    def vienna_wedding_constraint(arrive_vienna):
        duration = stay_durations['Vienna']
        return 6 <= arrive_vienna <= 10 - duration + 1
    
    def stockholm_friend_constraint(arrive_stockholm):
        duration = stay_durations['Stockholm']
        return 1 <= arrive_stockholm <= 3 - duration + 1
    
    def riga_conference_constraint(arrive_riga):
        duration = stay_durations['Riga']
        return 18 <= arrive_riga <= 20 - duration + 1
    
    problem.addConstraint(athens_workshop_constraint, ['arrive_Athens'])
    problem.addConstraint(valencia_show_constraint, ['arrive_Valencia'])
    problem.addConstraint(vienna_wedding_constraint, ['arrive_Vienna'])
    problem.addConstraint(stockholm_friend_constraint, ['arrive_Stockholm'])
    problem.addConstraint(riga_conference_constraint, ['arrive_Riga'])
    
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
    
    # Improved itinerary constraint
    def valid_itinerary(*arrivals):
        arrival_dict = {}
        for i, city in enumerate(cities):
            arrival_dict[city] = arrivals[i]
        
        # Create list of (arrival, city) pairs
        city_arrivals = [(arrival_dict[city], city) for city in cities]
        
        # Sort by arrival day to get visit order
        city_arrivals.sort()
        
        # Check if all arrival days are distinct
        arrival_days = [arrival for arrival, _ in city_arrivals]
        if len(set(arrival_days)) != len(arrival_days):
            return False
        
        # Check consecutive cities for flight connections and valid timing
        for i in range(len(city_arrivals) - 1):
            current_arrival, current_city = city_arrivals[i]
            next_arrival, next_city = city_arrivals[i + 1]
            
            # Check flight connection
            if (current_city, next_city) not in bidirectional_connections:
                return False
            
            # Check timing: next city must arrive after current city departure
            current_departure = current_arrival + stay_durations[current_city] - 1
            if next_arrival <= current_departure:
                return False
        
        # Check total trip duration
        first_arrival = city_arrivals[0][0]
        last_city = city_arrivals[-1][1]
        last_departure = arrival_dict[last_city] + stay_durations[last_city] - 1
        total_duration = last_departure - first_arrival + 1
        
        # Total trip should be exactly 29 days
        if total_duration != 29:
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