from z3 import *

def main():
    friends = ["Kenneth", "Lisa", "Joshua", "Nancy", "Andrew", "John"]
    n = len(friends)
    
    # Convert availability times to minutes from 9:00 AM
    available_start_relative = [
        735,  # Kenneth: 21:15 (21*60+15 - 9*60 = 735)
        0,     # Lisa: 9:00
        180,   # Joshua: 12:00 (12-9)*60=180
        0,     # Nancy: 8:00 -> available from start, but travel time applies
        150,   # Andrew: 11:30 (2*60+30=150)
        465    # John: 16:45 (7*60+45=465)
    ]
    available_end_relative = [
        780,  # Kenneth: 22:00 (13*60=780)
        450,   # Lisa: 16:30 (7*60+30=450)
        375,   # Joshua: 15:15 (6*60+15=375)
        150,   # Nancy: 11:30 (2*60+30=150)
        675,   # Andrew: 20:15 (11*60+15=675)
        750    # John: 21:30 (12*60+30=750)
    ]
    durations = [30, 45, 15, 90, 60, 75]  # minutes

    # Travel times from Embarcadero to each location
    travel_start = [21, 10, 5, 11, 10, 21]  # to Kenneth, Lisa, Joshua, Nancy, Andrew, John

    # Travel times between locations (6x6 matrix: [from][to])
    travel_matrix = [
        [0, 21, 22, 10, 17, 26],  # From Richmond (Kenneth)
        [20, 0, 9, 15, 9, 15],     # From Union Square (Lisa)
        [21, 9, 0, 13, 8, 19],     # From Financial (Joshua)
        [12, 12, 13, 0, 8, 22],    # From Pacific Heights (Nancy)
        [14, 7, 9, 8, 0, 19],      # From Nob Hill (Andrew)
        [25, 17, 19, 23, 20, 0]    # From Bayview (John)
    ]

    s = Optimize()

    meet_pos = [Int(f'meet_pos_{p}') for p in range(6)]
    
    # Constraints for meet_pos: each is either -1 or in [0,5]
    for p in range(6):
        s.add(Or(meet_pos[p] == -1, And(meet_pos[p] >= 0, meet_pos[p] <= 5)))
    
    # If a position is -1, all subsequent must be -1
    for p in range(5):
        s.add(If(meet_pos[p] == -1, meet_pos[p+1] == -1, True))
    
    # All included meetings are distinct
    for i in range(6):
        for j in range(i+1, 6):
            s.add(If(And(meet_pos[i] != -1, meet_pos[j] != -1), meet_pos[i] != meet_pos[j]))
    
    start_pos = [Int(f'start_pos_{p}') for p in range(6)]
    end_pos = [Int(f'end_pos_{p}') for p in range(6)]
    
    # Position 0: first meeting
    p0 = meet_pos[0]
    s.add(If(p0 != -1,
             And(
                 start_pos[0] >= travel_start[p0],
                 start_pos[0] >= available_start_relative[p0],
                 end_pos[0] == start_pos[0] + durations[p0],
                 end_pos[0] <= available_end_relative[p0]
             ),
             And(start_pos[0] == 0, end_pos[0] == 0)
    ))
    
    # Positions 1 to 5
    for p in range(1, 6):
        prev_index = meet_pos[p-1]
        curr_index = meet_pos[p]
        s.add(If(curr_index != -1,
                 And(
                     start_pos[p] >= end_pos[p-1] + travel_matrix[prev_index][curr_index],
                     start_pos[p] >= available_start_relative[curr_index],
                     end_pos[p] == start_pos[p] + durations[curr_index],
                     end_pos[p] <= available_end_relative[curr_index]
                 ),
                 True
        ))
    
    count = Int('count')
    s.add(count == Sum([If(meet_pos[p] != -1, 1, 0) for p in range(6)]))
    s.maximize(count)
    
    if s.check() == sat:
        m = s.model()
        meet_pos_vals = [m.evaluate(meet_pos[p]) for p in range(6)]
        start_pos_vals = [m.evaluate(start_pos[p]) for p in range(6)]
        end_pos_vals = [m.evaluate(end_pos[p]) for p in range(6)]
        
        itinerary = []
        for p in range(6):
            if meet_pos_vals[p].as_long() != -1:
                idx = meet_pos_vals[p].as_long()
                person = friends[idx]
                total_minutes_start = 540 + start_pos_vals[p].as_long()  # 9:00 AM is 540 minutes from midnight
                total_minutes_end = 540 + end_pos_vals[p].as_long()
                hours_start = total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                hours_end = total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                start_time = f"{hours_start:02d}:{minutes_start:02d}"
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
        
        print('SOLUTION:')
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()