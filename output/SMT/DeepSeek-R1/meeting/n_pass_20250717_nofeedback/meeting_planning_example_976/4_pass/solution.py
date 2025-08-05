from z3 import *

def main():
    s = [Int(f's_{i}') for i in range(6)]
    p = [Int(f'p_{i}') for i in range(6)]
    x = [Int(f'x_{i}') for i in range(6)]
    dur_x = [Int(f'dur_x_{i}') for i in range(6)]
    gaps = [Int(f'gap_{i}') for i in range(5)]
    
    durations = [75, 60, 15, 120, 60, 105]
    buildings = ['A', 'B', 'A', 'A', 'C', 'C']
    
    travel_matrix = [
        [15 if buildings[i] == buildings[j] else 30 for j in range(6)]
        for i in range(6)
    ]
    
    solver = Solver()
    
    for i in range(6):
        solver.add(s[i] >= 0)
        solver.add(s[i] <= 780 - durations[i])
        solver.add(s[i] % 15 == 0)
        solver.add(Or(s[i] + durations[i] <= 180, s[i] >= 240))
    
    for i in range(6):
        solver.add(p[i] >= 0, p[i] < 6)
    solver.add(Distinct(p))
    
    for i in range(6):
        solver.add(dur_x[i] == If(
            p[i] == 0, durations[0],
            If(p[i] == 1, durations[1],
            If(p[i] == 2, durations[2],
            If(p[i] == 3, durations[3],
            If(p[i] == 4, durations[4], durations[5])))))
        )
        solver.add(x[i] == If(
            p[i] == 0, s[0],
            If(p[i] == 1, s[1],
            If(p[i] == 2, s[2],
            If(p[i] == 3, s[3],
            If(p[i] == 4, s[4], s[5])))))
        )
    
    for i in range(5):
        solver.add(x[i] <= x[i+1])
    
    for i in range(5):
        travel_time = 0
        for m in range(6):
            for n in range(6):
                travel_time = If(And(p[i] == m, p[i+1] == n), travel_matrix[m][n], travel_time)
        solver.add(x[i+1] >= x[i] + dur_x[i] + travel_time)
        solver.add(gaps[i] == x[i+1] - (x[i] + dur_x[i]))
    
    group0 = Or(gaps[0] >= 45, gaps[1] >= 45, gaps[2] >= 45)
    group1 = Or(gaps[1] >= 45, gaps[2] >= 45, gaps[3] >= 45)
    group2 = Or(gaps[2] >= 45, gaps[3] >= 45, gaps[4] >= 45)
    solver.add(group0, group1, group2)
    
    if solver.check() == sat:
        model = solver.model()
        start_times = [model.evaluate(s[i]).as_long() for i in range(6)]
        names = ["Thomas", "Brian", "Nancy", "Jessica", "Mary", "Sarah"]
        schedule = []
        for i, name in enumerate(names):
            start = start_times[i]
            end = start + durations[i]
            start_hour = start // 60
            start_minute = start % 60
            end_hour = end // 60
            end_minute = end % 60
            start_str = f"{9 + start_hour}:{start_minute:02d}"
            end_str = f"{9 + end_hour}:{end_minute:02d}"
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        itinerary = sorted(schedule, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No valid schedule found")

if __name__ == '__main__':
    main()