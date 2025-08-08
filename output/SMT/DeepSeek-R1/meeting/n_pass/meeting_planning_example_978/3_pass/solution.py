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
    
    position = [Int(f'pos_{i}') for i in range(n)]
    for p in position:
        s.add(p >= 0, p < n)
    s.add(Distinct(position))
    
    start = [Int(f'start_{i}') for i in range(n)]
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
        schedule = []
        for i in range(n):
            pos_val = model[position[i]].as_long()
            start_val = model[start[i]].as_long()
            schedule.append((i, start_val, pos_val))
        
        schedule.sort(key=lambda x: x[2])
        
        def to_time(minutes):
            hour = 10 + minutes // 60
            minute = minutes % 60
            return f"{hour:02d}:{minute:02d}"
        
        itinerary = []
        for meet in schedule:
            i, s_time, _ = meet
            e_time = s_time + durations[i]
            itinerary.append({
                'action': 'meet',
                'person': names[i],
                'start_time': to_time(s_time),
                'end_time': to_time(e_time)
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()