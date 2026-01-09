import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    required_days = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    
    # Direct flight connections
    direct_flights = [
        ('Brussels', 'Valencia'), ('Rome', 'Valencia'), ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'), ('Dubrovnik', 'Geneva'), ('Valencia', 'Geneva'),
        ('Rome', 'Riga'), ('Geneva', 'Budapest'), ('Riga', 'Brussels'),
        ('Rome', 'Budapest'), ('Rome', 'Brussels'), ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for city1, city2 in direct_flights:
        bidirectional_flights.add((city1, city2))
        bidirectional_flights.add((city2, city1))
    
    # Total days
    total_days = 17
    
    # Define variables for visit order (position in itinerary)
    positions = list(range(len(cities)))
    problem.addVariables(cities, positions)
    problem.addConstraint(AllDifferentConstraint(), cities)
    
    # Helper function to check if two consecutive cities in itinerary are connected by direct flight
    def are_connected(city_order):
        for i in range(len(city_order) - 1):
            city1 = city_order[i]
            city2 = city_order[i + 1]
            if (city1, city2) not in bidirectional_flights:
                return False
        return True
    
    # Constraint: Cities must be connected by direct flights in the itinerary order
    def flight_connectivity_constraint(*assigned_cities):
        # Create ordered list of cities based on their positions
        city_order = [None] * len(cities)
        for city, pos in zip(cities, assigned_cities):
            city_order[pos] = city
        
        # Remove None values (shouldn't happen with AllDifferentConstraint)
        city_order = [city for city in city_order if city is not None]
        
        return are_connected(city_order)
    
    problem.addConstraint(flight_connectivity_constraint, cities)
    
    # Constraint: Total days must equal 17
    def total_days_constraint(*assigned_cities):
        return sum(required_days.values()) == total_days
    
    # Special constraints
    def brussels_workshop_constraint(*assigned_cities):
        brussels_pos = assigned_cities[cities.index('Brussels')]
        brussels_days = required_days['Brussels']
        
        # Brussels must include days 7-11 for workshop
        # This means Brussels visit must overlap with days 7-11
        brussels_start = sum(required_days[city] for city, pos in zip(cities, assigned_cities) if pos < brussels_pos)
        brussels_end = brussels_start + brussels_days
        
        # Check if Brussels visit overlaps with days 7-11
        return brussels_start <= 11 and brussels_end >= 7
    
    def budapest_friend_constraint(*assigned_cities):
        budapest_pos = assigned_cities[cities.index('Budapest')]
        budapest_days = required_days['Budapest']
        
        # Budapest must include day 16-17 for meeting friend
        budapest_start = sum(required_days[city] for city, pos in zip(cities, assigned_cities) if pos < budapest_pos)
        budapest_end = budapest_start + budapest_days
        
        # Check if Budapest visit includes days 16-17
        return budapest_start <= 16 and budapest_end >= 16
    
    def riga_friends_constraint(*assigned_cities):
        riga_pos = assigned_cities[cities.index('Riga')]
        riga_days = required_days['Riga']
        
        # Riga must include days 4-7 for touring with friends
        riga_start = sum(required_days[city] for city, pos in zip(cities, assigned_cities) if pos < riga_pos)
        riga_end = riga_start + riga_days
        
        # Check if Riga visit overlaps with days 4-7
        return riga_start <= 7 and riga_end >= 4
    
    problem.addConstraint(brussels_workshop_constraint, cities)
    problem.addConstraint(budapest_friend_constraint, cities)
    problem.addConstraint(riga_friends_constraint, cities)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create ordered itinerary
    itinerary_order = []
    for pos in range(len(cities)):
        for city in cities:
            if solution[city] == pos:
                itinerary_order.append(city)
                break
    
    # Calculate day ranges
    itinerary = []
    current_day = 1
    
    for city in itinerary_order:
        days = required_days[city]
        if days == 1:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{current_day + days - 1}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day += days
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))