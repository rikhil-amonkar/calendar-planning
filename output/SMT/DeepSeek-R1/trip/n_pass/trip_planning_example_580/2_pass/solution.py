from z3 import *

def main():
    s = Solver()
    
    base_durations = [6, 6, 6, 6, 2]
    reduced_durations = [3, 3, 3, 3, 1]
    city_names = ['Geneva', 'Porto', 'Paris', 'Oslo', 'Reykjavik']
    
    reduced_flags = [Bool(f'reduced_{i}') for i in range(5)]
    s.add(Sum([If(flag, 1, 0) for flag in reduced_flags]) == 1)
    
    durations = [If(reduced_flags[i], reduced_durations[i], base_durations[i]) for i in range(5)]
    
    order = [Int(f'order_{i}') for i in range(5)]
    for i in range(5):
        s.add(order[i] >= 0, order[i] < 5)
    s.add(Distinct(order))
    
    starts = [Int(f'start_{i}') for i in range(5)]
    ends = [Int(f'end_{i}') for i in range(5)]
    
    for i in range(5):
        s.add(ends[i] == starts[i] + durations[i] - 1)
    
    s.add(starts[order[0]] == 1)
    for i in range(1, 5):
        s.add(starts[order[i]] == ends[order[i-1]] + 1)
    s.add(ends[order[4]] == 23)
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(5)]
        itinerary = []
        for idx in order_val:
            start_val = model.evaluate(starts[idx]).as_long()
            end_val = model.evaluate(ends[idx]).as_long()
            itinerary.append({
                'day_range': f'Day {start_val}-{end_val}',
                'place': city_names[idx]
            })
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()