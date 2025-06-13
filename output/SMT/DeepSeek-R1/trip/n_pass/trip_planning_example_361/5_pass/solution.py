from z3 import Solver, Bool, Or, And, Not, If, Sum, sat, Implies

def main():
    s = Solver()
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    days = 15
    in_city = {city: [Bool(f'in_{city}_{i}') for i in range(days) for city in cities}
    
    # Flight connection graph
    graph = {
        'Paris': ['Madrid', 'Bucharest'],
        'Madrid': ['Paris', 'Seville'],
        'Bucharest': ['Paris', 'Seville'],
        'Seville': ['Madrid', 'Bucharest']
    }
    
    # Constraint: Each day, the traveler is in at least one city
    for i in range(days):
        s.add(Or(in_city['Paris'][i], in_city['Madrid'][i], in_city['Bucharest'][i], in_city['Seville'][i]))
    
    # Constraint: At most two cities per day
    for i in range(days):
        s.add(Not(And(in_city['Paris'][i], in_city['Madrid'][i], in_city['Bucharest'][i])))
        s.add(Not(And(in_city['Paris'][i], in_city['Madrid'][i], in_city['Seville'][i])))
        s.add(Not(And(in_city['Paris'][i], in_city['Bucharest'][i], in_city['Seville'][i])))
        s.add(Not(And(in_city['Madrid'][i], in_city['Bucharest'][i], in_city['Seville'][i])))
    
    # Constraint: Bucharest and Seville cannot be together on any day
    for i in range(days):
        s.add(Not(And(in_city['Bucharest'][i], in_city['Seville'][i])))
    
    # Constraint: Consecutive days must share at least one common city
    for i in range(days - 1):
        s.add(Or(
            And(in_city['Paris'][i], in_city['Paris'][i+1]),
            And(in_city['Madrid'][i], in_city['Madrid'][i+1]),
            And(in_city['Bucharest'][i], in_city['Bucharest'][i+1]),
            And(in_city['Seville'][i], in_city['Seville'][i+1])
        ))
    
    # Movement constraint: Each city must be reachable from previous day
    for i in range(1, days):
        for c in cities:
            options = [in_city[c][i-1]]  # Stay in same city
            for neighbor in graph[c]:
                options.append(in_city[neighbor][i-1])
            s.add(Implies(in_city[c][i], Or(options)))
    
    # Fixed constraints: Madrid on days 1-7 (indices 0-6)
    for i in range(7):
        s.add(in_city['Madrid'][i])
    
    # Fixed constraints: Bucharest on days 14-15 (indices 13-14)
    s.add(in_city['Bucharest'][13])
    s.add(in_city['Bucharest'][14])
    
    # Total days in Paris must be 6
    paris_days = Sum([If(in_city['Paris'][i], 1, 0) for i in range(days)])
    s.add(paris_days == 6)
    
    # Total days in Seville must be 3
    seville_days = Sum([If(in_city['Seville'][i], 1, 0) for i in range(days)])
    s.add(seville_days == 3)
    
    # Solve and output the schedule
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(days):
            present_cities = []
            for city in cities:
                if m.evaluate(in_city[city][i]):
                    present_cities.append(city)
            schedule.append((i + 1, present_cities))
        
        for day, cities_list in schedule:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()