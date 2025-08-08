from z3 import *
import json

def main():
    # City indices
    T, B, S, St, M, Mi = 0, 1, 2, 3, 4, 5
    city_names = {
        T: "Tallinn",
        B: "Bucharest",
        S: "Seville",
        St: "Stockholm",
        M: "Munich",
        Mi: "Milan"
    }
    durations = [2, 4, 5, 5, 5, 2]  # T, B, S, St, M, Mi
    
    edges = [
        (Mi, St), (M, St), (B, M), (M, S), (St, T), (M, Mi), (M, T), (S, Mi)
    ]
    directed_edges = []
    for a, b in edges:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    s = Solver()
    block = [Int('b%d' % i) for i in range(6)]
    
    for i in range(6):
        s.add(block[i] >= 0, block[i] <= 5)
    s.add(Distinct(block))
    
    def duration(city):
        return If(city == T, 2,
                If(city == B, 4,
                If(city == S, 5,
                If(city == St, 5,
                If(city == M, 5,
                If(city == Mi, 2, 0))))))
    
    d0 = duration(block[0])
    d1 = duration(block[1])
    d2 = duration(block[2])
    d3 = duration(block[3])
    d4 = duration(block[4])
    d5 = duration(block[5])
    
    s0 = 1
    s1 = d0
    s2 = d0 + d1 - 1
    s3 = d0 + d1 + d2 - 2
    s4 = d0 + d1 + d2 + d3 - 3
    s5 = d0 + d1 + d2 + d3 + d4 - 4
    
    def adjacent(i, j):
        options = []
        for a, b in directed_edges:
            options.append(And(i == a, j == b))
        return Or(options)
    
    for i in range(5):
        s.add(adjacent(block[i], block[i+1]))
    
    bucharest_constraint = Or(
        And(block[0] == B, s0 <= 4),
        And(block[1] == B, s1 <= 4),
        And(block[2] == B, s2 <= 4),
        And(block[3] == B, s3 <= 4),
        And(block[4] == B, s4 <= 4),
        And(block[5] == B, s5 <= 4)
    )
    
    seville_constraint = Or(
        And(block[0] == S, And(s0 >= 4, s0 <= 12)),
        And(block[1] == S, And(s1 >= 4, s1 <= 12)),
        And(block[2] == S, And(s2 >= 4, s2 <= 12)),
        And(block[3] == S, And(s3 >= 4, s3 <= 12)),
        And(block[4] == S, And(s4 >= 4, s4 <= 12)),
        And(block[5] == S, And(s5 >= 4, s5 <= 12))
    )
    
    munich_constraint = Or(
        And(block[0] == M, s0 <= 8),
        And(block[1] == M, s1 <= 8),
        And(block[2] == M, s2 <= 8),
        And(block[3] == M, s3 <= 8),
        And(block[4] == M, s4 <= 8),
        And(block[5] == M, s5 <= 8)
    )
    
    s.add(bucharest_constraint)
    s.add(seville_constraint)
    s.add(munich_constraint)
    
    if s.check() == sat:
        model = s.model()
        block_order_val = [model.evaluate(block[i]).as_long() for i in range(6)]
        durs_val = [durations[city] for city in block_order_val]
        
        e = [0] * 6
        e[0] = 1 + durs_val[0] - 1
        for i in range(1, 6):
            e[i] = e[i-1] + durs_val[i] - 1
        
        flight_days = set(e[:5])
        itinerary = []
        for d in range(1, 19):
            if d in flight_days:
                for i in range(5):
                    if e[i] == d:
                        itinerary.append((d, block_order_val[i]))
                        itinerary.append((d, block_order_val[i+1]))
                        break
            else:
                if d <= e[0]:
                    block_id = 0
                elif d <= e[1]:
                    block_id = 1
                elif d <= e[2]:
                    block_id = 2
                elif d <= e[3]:
                    block_id = 3
                elif d <= e[4]:
                    block_id = 4
                else:
                    block_id = 5
                itinerary.append((d, block_order_val[block_id]))
        
        itinerary_dict = []
        for day, city_idx in itinerary:
            itinerary_dict.append({"day": day, "place": city_names[city_idx]})
        
        result = {"itinerary": itinerary_dict}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()