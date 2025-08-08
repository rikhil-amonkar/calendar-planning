from z3 import *

def main():
    s = Solver()
    
    base_durations = [6, 6, 6, 6, 2]
    reduced_durations = [3, 3, 3, 3, 1]
    city_names = ['Geneva', 'Porto', 'Paris', 'Oslo', 'Reykjavik']
    
    # Exactly one city must be reduced
    reduced_flags = [Bool(f'reduced_{i}') for i in range(5)]
    s.add(Sum([If(flag, 1, 0) for flag in reduced_flags]) == 1)
    
    # City assignment to positions 0-4
    city_at_pos = [Int(f'city_at_pos_{k}') for k in range(5)]
    for k in range(5):
        s.add(city_at_pos[k] >= 0, city_at_pos[k] <= 4)
    s.add(Distinct(city_at_pos))
    
    # Start and end days for each position
    pos_start = [Int(f'pos_start_{k}') for k in range(5)]
    pos_end = [Int(f'pos_end_{k}') for k in range(5)]
    
    # First position starts at day 1
    s.add(pos_start[0] == 1)
    
    # Create contiguous schedule
    for k in range(5):
        city_idx = city_at_pos[k]
        dur_k = Int(f'dur_k_{k}')
        
        # Set duration based on reduction status
        for i in range(5):
            duration_val = If(reduced_flags[i], reduced_durations[i], base_durations[i])
            s.add(If(city_idx == i, dur_k == duration_val, True))
            
        # End day calculation
        s.add(pos_end[k] == pos_start[k] + dur_k - 1)
        
        # Next position starts after current ends
        if k < 4:
            s.add(pos_start[k+1] == pos_end[k] + 1)
    
    # Entire trip must end on day 23
    s.add(pos_end[4] == 23)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for k in range(5):
            city_index = model.evaluate(city_at_pos[k]).as_long()
            start_val = model.evaluate(pos_start[k]).as_long()
            end_val = model.evaluate(pos_end[k]).as_long()
            itinerary.append({
                'day_range': f'Day {start_val}-{end_val}',
                'place': city_names[city_index]
            })
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()