from z3 import *

def main():
    meetings = [
        (0, "Lisa", 15, "A"),
        (1, "Joshua", 15, "B"),
        (2, "Joseph", 45, "C"),
        (3, "Betty", 60, "D"),
        (4, "John", 45, "E"),
        (5, "Sarah", 105, "F"),
        (6, "Daniel", 60, "G"),
        (7, "Melissa", 120, "H"),
        (8, "Andrew", 105, "I")
    ]
    
    adjacencies = {
        "A": ["B", "D"],
        "B": ["A", "C"],
        "C": ["B", "D"],
        "D": ["A", "C", "E", "G"],
        "E": ["D", "F"],
        "F": ["E", "G"],
        "G": ["D", "F", "H", "I"],
        "H": ["G", "I"],
        "I": ["G", "H"]
    }
    
    names = [m[1] for m in meetings]
    durations = [m[2] for m in meetings]
    buildings = [m[3] for m in meetings]
    
    n = len(meetings)
    travel_matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                b1 = buildings[i]
                b2 = buildings[j]
                if b1 == b2:
                    travel_matrix[i][j] = 0
                elif b2 in adjacencies[b1]:
                    travel_matrix[i][j] = 15
                else:
                    travel_matrix[i][j] = 30
    
    s = Solver()
    s.set("timeout", 300000)
    
    position = [Int('pos_%d' % i) for i in range(n)]
    for p in position:
        s.add(p >= 0, p < n)
    s.add(Distinct(position))
    
    start = [Int('start_%d' % i) for i in range(n)]
    for i in range(n):
        s.add(start[i] >= 0)
        s.add(start[i] + durations[i] <= 720)
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            cond = (position[j] == position[i] + 1)
            constraint = (start[i] + durations[i] + travel_matrix[i][j] <= start[j])
            s.add(Implies(cond, constraint))
    
    if s.check() == sat:
        model = s.model()
        start_times = []
        for i in range(n):
            pos_val = model.evaluate(position[i])
            start_val = model.evaluate(start[i])
            if not (is_algebraic_value(start_val) or not (is_algebraic_value(pos_val)):
                continue
            start_times.append((i, start_val.as_long(), pos_val.as_long()))
        
        def minutes_to_time(mins):
            total_mins = mins
            hour = 10 + total_mins // 60
            minute = total_mins % 60
            return f"{hour:02d}:{minute:02d}"
        
        itinerary = []
        for i, s_time, pos in start_times:
            end_time = s_time + durations[i]
            itinerary.append({
                'action': 'meet',
                'person': names[i],
                'start_time': minutes_to_time(s_time),
                'end_time': minutes_to_time(end_time)
            })
        
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        print(f"Plan found: {{'itinerary': {itinerary_sorted}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()