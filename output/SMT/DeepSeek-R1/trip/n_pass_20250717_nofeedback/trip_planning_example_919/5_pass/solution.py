from z3 import *

def main():
    # City indices and their required stay durations
    city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    L_arr = [4, 2, 3, 2, 3, 4, 3]  # days per city

    # Directed flight connections
    directed_edges = set()
    bidirectional_pairs = [
        (3, 6), (2, 6), (0, 1), (0, 5), (0, 4), (3, 1), (4, 6), (2, 4),
        (0, 3), (0, 2), (1, 6), (0, 6), (5, 6), (5, 1), (3, 4), (1, 4)
    ]
    for u, v in bidirectional_pairs:
        directed_edges.add((u, v))
        directed_edges.add((v, u))
    oneway_edges = [(2, 3), (3, 5)]  # Rome to Riga, Riga to Vilnius
    for u, v in oneway_edges:
        directed_edges.add((u, v))

    # Z3 variables for city permutation
    c = [Int('c_%d' % i) for i in range(7)]
    # Start and end days
    S = [Int('S_%d' % i) for i in range(7)]
    E = [Int('E_%d' % i) for i in range(7)]
    
    s = Solver()
    
    # Fixed positions: Vienna first, Lisbon fifth, Oslo sixth
    s.add(c[0] == 0)  # Vienna
    s.add(c[5] == 4)  # Lisbon
    s.add(c[6] == 6)  # Oslo
    
    # Middle cities: positions 1-4 are permutation of Milan(1), Rome(2), Riga(3), Vilnius(5)
    middle_indices = [1, 2, 3, 5]
    s.add(Distinct([c[1], c[2], c[3], c[4]]))
    for i in range(1, 5):
        s.add(Or([c[i] == idx for idx in middle_indices]))
    
    # Last middle city must have flight to Lisbon (cannot be Vilnius)
    s.add(Or(c[4] == 1, c[4] == 2, c[4] == 3))
    
    # Duration helper function
    def get_duration(city_var):
        return If(city_var == 0, 4,
               If(city_var == 1, 2,
               If(city_var == 2, 3,
               If(city_var == 3, 2,
               If(city_var == 4, 3,
               If(city_var == 5, 4,
               If(city_var == 6, 3, 0)))))))
    
    # Start/end days with flight day overlaps
    s.add(S[0] == 1)  # Vienna starts on day 1
    s.add(E[0] == S[0] + get_duration(c[0]) - 1)  # Vienna ends on day 4
    
    # Chain for subsequent cities
    for i in range(1, 7):
        s.add(S[i] == E[i-1])  # Next city starts when previous ends (flight day overlap)
        s.add(E[i] == S[i] + get_duration(c[i]) - 1)
    
    # Explicit start days for Lisbon and Oslo
    s.add(S[5] == 11)  # Lisbon starts on day 11
    s.add(S[6] == 13)  # Oslo starts on day 13
    
    # Flight connections between consecutive cities
    for i in range(6):
        options = []
        for edge in directed_edges:
            options.append(And(c[i] == edge[0], c[i+1] == edge[1]))
        s.add(Or(options))
    
    # Total trip must end on day 15
    s.add(E[6] == 15)
    
    # Solve and generate itinerary
    if s.check() == sat:
        model = s.model()
        perm = [model.eval(c[i]).as_long() for i in range(7)]
        start_days = [model.eval(S[i]).as_long() for i in range(7)]
        end_days = [model.eval(E[i]).as_long() for i in range(7)]
        
        # Create daily itinerary
        itinerary = []
        for day in range(1, 16):
            cities_today = []
            for idx in range(7):
                if start_days[idx] <= day <= end_days[idx]:
                    cities_today.append(city_names[perm[idx]])
            itinerary.append({"day": day, "city": cities_today})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()