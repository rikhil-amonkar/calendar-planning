import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    required_days = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    
    # Direct flight connections
    direct_flights = [
        ('Stuttgart', 'Split'),
        ('Prague', 'Florence'),
        ('Krakow', 'Stuttgart'),
        ('Krakow', 'Split'),
        ('Split', 'Prague'),
        ('Krakow', 'Prague')
    ]
    
    # Make flights bidirectional
    flights = set()
    for city1, city2 in direct_flights:
        flights.add((city1, city2))
        flights.add((city2, city1))
    
    # Variables: day 1 to day 8, each day has a city
    days = list(range(1, 9))
    for day in days:
        problem.addVariable(day, cities)
    
    # Constraint 1: Total days in each city must match requirements
    for city in cities:
        problem.addConstraint(lambda *assignments, c=city: assignments.count(c) == required_days[c], days)
    
    # Constraint 2: Can only fly between cities with direct flights
    def flight_constraint(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        return (day1_city, day2_city) in flights
    
    for i in range(1, 8):
        problem.addConstraint(flight_constraint, [i, i+1])
    
    # Constraint 3: Stay in Prague for 4 consecutive days
    def prague_consecutive(*assignments):
        prague_days = [i+1 for i, city in enumerate(assignments) if city == 'Prague']
        if not prague_days:
            return False
        return max(prague_days) - min(prague_days) + 1 == 4
    
    problem.addConstraint(prague_consecutive, days)
    
    # Constraint 4: Stay in Stuttgart for 2 consecutive days
    def stuttgart_consecutive(*assignments):
        stuttgart_days = [i+1 for i, city in enumerate(assignments) if city == 'Stuttgart']
        if len(stuttgart_days) != 2:
            return False
        return stuttgart_days[1] - stuttgart_days[0] == 1
    
    problem.addConstraint(stuttgart_consecutive, days)
    
    # Constraint 5: Wedding in Stuttgart between day 2 and day 3
    # This means Stuttgart must be visited on day 2 OR day 3 (or both)
    def wedding_constraint(day2, day3):
        return day2 == 'Stuttgart' or day3 == 'Stuttgart'
    
    problem.addConstraint(wedding_constraint, [2, 3])
    
    # Constraint 6: Stay in Split for 2 consecutive days
    def split_consecutive(*assignments):
        split_days = [i+1 for i, city in enumerate(assignments) if city == 'Split']
        if len(split_days) != 2:
            return False
        return split_days[1] - split_days[0] == 1
    
    problem.addConstraint(split_consecutive, days)
    
    # Constraint 7: Meet friends in Split between day 3 and day 4
    # This means Split must be visited on day 3 OR day 4 (or both)
    def friends_constraint(day3, day4):
        return day3 == 'Split' or day4 == 'Split'
    
    problem.addConstraint(friends_constraint, [3, 4])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
    
    # Take the first valid solution
    solution = solutions[0]
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, 9):
        if solution[day] != current_city:
            end_day = day - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
            current_city = solution[day]
            start_day = day
    
    # Add the last segment
    itinerary.append({
        "day_range": f"Day {start_day}-8",
        "place": current_city
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()