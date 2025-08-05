from z3 import *

def main():
    s = Solver()
    n_days = 16
    cities = ["London", "Oslo", "Split", "Porto"]
    I = [Int(f"I_{i}") for i in range(n_days)]
    
    # Each day must be one of the cities: 0,1,2,3
    for i in range(n_days):
        s.add(Or(I[i] == 0, I[i] == 1, I[i] == 2, I[i] == 3))
    
    # Split must be from day7 to day11 (inclusive): indices 6 to 10
    for i in [6,7,8,9,10]:
        s.add(I[i] == 2)
    
    # Allowed direct flight pairs: (0,1), (1,0), (0,2), (2,0), (1,2), (2,1), (1,3), (3,1)
    for i in range(1, n_days):
        s.add(Or(
            I[i] == I[i-1],
            And(I[i-1] == 0, I[i] == 1),
            And(I[i-1] == 1, I[i] == 0),
            And(I[i-1] == 0, I[i] == 2),
            And(I[i-1] == 2, I[i] == 0),
            And(I[i-1] == 1, I[i] == 2),
            And(I[i-1] == 2, I[i] == 1),
            And(I[i-1] == 1, I[i] == 3),
            And(I[i-1] == 3, I[i] == 1)
        ))
    
    # Presence matrix: 4 cities x 16 days
    presence = [[Bool(f"presence_{c}_{i}") for i in range(n_days)] for c in range(4)]
    
    # Define presence for day0
    for c in range(4):
        s.add(presence[c][0] == (I[0] == c))
    
    for i in range(1, n_days):
        for c in range(4):
            # On travel days, present in both departure and arrival cities
            s.add(presence[c][i] == Or(
                And(I[i] == I[i-1], I[i] == c),  # No travel: only current city
                And(I[i] != I[i-1], Or(I[i] == c, I[i-1] == c))  # Travel: both cities
            )
    
    # Total days per city
    total_days = [0]*4
    for c in range(4):
        total_days[c] = Sum([If(presence[c][i], 1, 0) for i in range(n_days)])
    s.add(total_days[0] == 7)  # London
    s.add(total_days[1] == 2)  # Oslo
    s.add(total_days[2] == 5)  # Split
    s.add(total_days[3] == 5)  # Porto
    
    # Must be in London on at least one day between day1 and day7 (indices 0 to 6)
    s.add(Or([presence[0][i] for i in range(7)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(n_days):
            city_index = m[I[i]].as_long()
            itinerary_list.append({"day": i+1, "place": cities[city_index]})
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()