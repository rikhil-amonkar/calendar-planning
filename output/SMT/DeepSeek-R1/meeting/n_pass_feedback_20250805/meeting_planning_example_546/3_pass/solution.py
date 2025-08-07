from z3 import *

def main():
    friends = ["Kenneth", "Lisa", "Joshua", "Nancy", "Andrew", "John"]
    n = len(friends)
    
    # Convert times to minutes from midnight
    available_start = [21*60+15, 9*60, 12*60, 8*60, 11*60+30, 16*60+45]  # 9:15PM, 9:00AM, 12:00PM, 8:00AM, 11:30AM, 4:45PM
    available_end = [22*60, 16*60+30, 15*60+15, 11*60+30, 20*60+15, 21*60+30]  # 10:00PM, 4:30PM, 3:15PM, 11:30AM, 8:15PM, 9:30PM
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
    
    # Helper functions for symbolic lookups
    def lookup_1d(arr, idx):
        expr = 0
        for i in range(len(arr)):
            expr = If(idx == i, arr[i], expr)
        return expr

    def lookup_2d(mat, row, col):
        expr = 0
        for i in range(len(mat)):
            for j in range(len(mat[i])):
                expr = If(And(row == i, col == j), mat[i][j], expr)
        return expr
    
    # Variables for meeting positions and times
    meet_pos = [Int(f'meet_pos_{p}') for p in range(6)]
    start_pos = [Int(f'start_pos_{p}') for p in range(6)]
    end_pos = [Int(f'end_pos_{p}') for p in range(6)]
    
    # Constraints for meet_pos: each is either -1 or in [0,5]
    for p in range(6):
        s.add(Or(meet_pos[p] == -1, And(meet_pos[p] >= 0, meet_pos[p] < n)))
    
    # If a position is -1, all subsequent must be -1
    for p in range(5):
        s.add(If(meet_pos[p] == -1, meet_pos[p+1] == -1, True))
    
    # All included meetings are distinct
    for i in range(6):
        for j in range(i+1, 6):
            s.add(If(And(meet_pos[i] != -1, meet_pos[j] != -1), meet_pos[i] != meet_pos[j], True))
    
    # Base time: arrive at Embarcadero at 9:00 AM (540 minutes)
    base_time = 540
    
    # Position 0: first meeting
    s.add(If(meet_pos[0] != -1,
             And(
                 start_pos[0] >= base_time + lookup_1d(travel_start, meet_pos[0]),
                 start_pos[0] >= lookup_1d(available_start, meet_pos[0]),
                 end_pos[0] == start_pos[0] + lookup_1d(durations, meet_pos[0]),
                 end_pos[0] <= lookup_1d(available_end, meet_pos[0])
             ),
             And(start_pos[0] == 0, end_pos[0] == 0)
    ))
    
    # Positions 1 to 5
    for p in range(1, 6):
        travel_expr = lookup_2d(travel_matrix, meet_pos[p-1], meet_pos[p])
        
        s.add(If(meet_pos[p] != -1,
                 And(
                     start_pos[p] >= end_pos[p-1] + travel_expr,
                     start_pos[p] >= lookup_1d(available_start, meet_pos[p]),
                     end_pos[p] == start_pos[p] + lookup_1d(durations, meet_pos[p]),
                     end_pos[p] <= lookup_1d(available_end, meet_pos[p])
                 ),
                 And(start_pos[p] == 0, end_pos[p] == 0)
        ))
    
    # Maximize the number of meetings
    count = Int('count')
    s.add(count == Sum([If(meet_pos[p] != -1, 1, 0) for p in range(6)]))
    s.maximize(count)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for p in range(6):
            if m.evaluate(meet_pos[p]).as_long() != -1:
                idx = m.evaluate(meet_pos[p]).as_long()
                person = friends[idx]
                start_min = m.evaluate(start_pos[p]).as_long()
                end_min = m.evaluate(end_pos[p]).as_long()
                # Convert minutes to HH:MM
                start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
                itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
        
        print('SOLUTION:')
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()