from z3 import *
import json

def main():
    # Define the duration function for each city index
    def dur(city_idx):
        return If(city_idx == 0, 2,
               If(city_idx == 1, 2,
               If(city_idx == 2, 4,
               If(city_idx == 3, 6,
               If(city_idx == 4, 7, 0)))))

    # Define allowed pairs for direct flights (undirected)
    allowed_pairs = set()
    edges = [(2,4), (4,3), (1,3), (4,1), (3,0), (2,3)]
    for (a, b) in edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))

    # Initialize solver
    s = Solver()
    
    # Create order variables for the 5 segments
    order = [Int('order%d' % i) for i in range(5)]
    
    # Constraints: each order variable must be between 0 and 4 (inclusive)
    for i in range(5):
        s.add(And(order[i] >= 0, order[i] <= 4))
    
    # Constraint: all order variables must be distinct
    s.add(Distinct(order))
    
    # Define start and end days for each segment
    start0 = 1
    end0 = start0 + dur(order[0]) - 1

    start1 = 1 + dur(order[0]) - 1
    end1 = start1 + dur(order[1]) - 1

    start2 = 1 + dur(order[0]) + dur(order[1]) - 2
    end2 = start2 + dur(order[2]) - 1

    start3 = 1 + dur(order[0]) + dur(order[1]) + dur(order[2]) - 3
    end3 = start3 + dur(order[3]) - 1

    start4 = 1 + dur(order[0]) + dur(order[1]) + dur(order[2]) + dur(order[3]) - 4
    end4 = start4 + dur(order[4]) - 1

    # Constraint: total trip must end on day 17
    s.add(end4 == 17)
    
    # Define Geneva and Munich constraints based on their city indices (2 for Geneva, 4 for Munich)
    geneva_start = If(order[0] == 2, start0,
                    If(order[1] == 2, start1,
                    If(order[2] == 2, start2,
                    If(order[3] == 2, start3, start4))))
    
    geneva_end = If(order[0] == 2, end0,
                  If(order[1] == 2, end1,
                  If(order[2] == 2, end2,
                  If(order[3] == 2, end3, end4))))
    
    munich_start = If(order[0] == 4, start0,
                    If(order[1] == 4, start1,
                    If(order[2] == 4, start2,
                    If(order[3] == 4, start3, start4))))
    
    munich_end = If(order[0] == 4, end0,
                  If(order[1] == 4, end1,
                  If(order[2] == 4, end2,
                  If(order[3] == 4, end3, end4))))
    
    # Constraints: Geneva must be between day 1 and 4, Munich between day 4 and 10
    s.add(geneva_start >= 1)
    s.add(geneva_end <= 4)
    s.add(munich_start >= 4)
    s.add(munich_end <= 10)
    
    # Constraints: consecutive cities must have direct flights
    for i in range(4):
        conds = []
        for pair in allowed_pairs:
            conds.append(And(order[i] == pair[0], order[i+1] == pair[1]))
        s.add(Or(conds))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]) for i in range(5)]
        start0_val = m.evaluate(start0)
        end0_val = m.evaluate(end0)
        start1_val = m.evaluate(start1)
        end1_val = m.evaluate(end1)
        start2_val = m.evaluate(start2)
        end2_val = m.evaluate(end2)
        start3_val = m.evaluate(start3)
        end3_val = m.evaluate(end3)
        start4_val = m.evaluate(start4)
        end4_val = m.evaluate(end4)
        
        city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
        
        itinerary = []
        segments = [
            (start0_val, end0_val, order_val[0]),
            (start1_val, end1_val, order_val[1]),
            (start2_val, end2_val, order_val[2]),
            (start3_val, end3_val, order_val[3]),
            (start4_val, end4_val, order_val[4])
        ]
        
        for seg in segments:
            start, end, city_idx = seg
            itinerary.append({
                "day_range": "Day {}-{}".format(start, end),
                "place": city_names[city_idx.as_long()]
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()