from z3 import *

def main():
    # Define travel matrix: 8x8, [from][to]
    # Indices: 0=Alamo, 1=Russian, 2=Presidio, 3=Chinatown, 4=Sunset, 5=Castro, 6=Embarcadero, 7=GoldenGate
    travel_matrix = [
        [0, 13, 18, 16, 16, 8, 17, 9],
        [15, 0, 14, 9, 23, 21, 8, 21],
        [18, 14, 0, 21, 15, 21, 20, 12],
        [17, 7, 19, 0, 29, 22, 5, 23],
        [17, 24, 16, 30, 0, 17, 31, 11],
        [8, 18, 20, 20, 17, 0, 22, 11],
        [19, 8, 20, 7, 30, 25, 0, 25],
        [10, 19, 11, 23, 10, 13, 25, 0]
    ]
    
    # Friend data: [name, window_start, window_end, min_duration, loc_index]
    friends = [
        ("Emily", 195, 315, 105, 1),    # Russian Hill
        ("Mark", 345, 630, 60, 2),       # Presidio
        ("Deborah", 0, 390, 45, 3),      # Chinatown (window_start adjusted to 0)
        ("Margaret", 750, 810, 60, 4),   # Sunset District
        ("George", 0, 315, 60, 5),       # The Castro (window_start adjusted to 0)
        ("Andrew", 675, 780, 75, 6),     # Embarcadero
        ("Steven", 135, 735, 105, 7)     # Golden Gate Park
    ]
    n_friends = len(friends)
    max_positions = n_friends
    
    # Create lists for friend attributes
    names = [f[0] for f in friends]
    window_start = [f[1] for f in friends]
    window_end = [f[2] for f in friends]
    min_duration = [f[3] for f in friends]
    loc_index = [f[4] for f in friends]
    
    s = Solver()
    
    # Sequence variables: seq[p] for position p, each is an integer: -1 or friend index (0..n_friends-1)
    seq = [Int('seq_%d' % p) for p in range(max_positions)]
    meet = [Bool('meet_%d' % i) for i in range(n_friends)]
    start_time = [Int('start_time_%d' % p) for p in range(max_positions)]
    
    # Constraints for sequence
    for p in range(max_positions):
        s.add(Or(seq[p] == -1, And(seq[p] >= 0, seq[p] < n_friends)))
        if p > 0:
            s.add(If(seq[p] != -1, seq[p-1] != -1, True))
            s.add(If(seq[p-1] == -1, seq[p] == -1, True))
    
    # Constraints for meet: friend i is met iff it appears in the sequence
    for i in range(n_friends):
        s.add(meet[i] == Or([seq[p] == i for p in range(max_positions)]))
    
    # Distinctness: each friend appears at most once in the sequence
    for p in range(max_positions):
        for q in range(p+1, max_positions):
            s.add(If(And(seq[p] >= 0, seq[q] >= 0), seq[p] != seq[q], True))
    
    # Constraints for start_time and meeting windows
    for p in range(max_positions):
        if p == 0:
            # For the first position
            friend0 = seq[0]
            # If there is a friend at position0, then set constraints
            arrival0 = Int('arrival0')
            s.add(If(friend0 >= 0,
                     And(
                         arrival0 == travel_matrix[0][loc_index[friend0]],
                         start_time[0] == If(arrival0 >= window_start[friend0], arrival0, window_start[friend0]),
                         start_time[0] >= window_start[friend0],
                         start_time[0] + min_duration[friend0] <= window_end[friend0]
                     ),
                     True
                  ))
        else:
            friend_prev = seq[p-1]
            friend_curr = seq[p]
            # Only if both the current and previous friends are present
            arrival_p = Int('arrival_%d' % p)
            s.add(If(And(friend_curr >= 0, friend_prev >= 0),
                     And(
                         arrival_p == start_time[p-1] + min_duration[friend_prev] + travel_matrix[loc_index[friend_prev]][loc_index[friend_curr]],
                         start_time[p] == If(arrival_p >= window_start[friend_curr], arrival_p, window_start[friend_curr]),
                         start_time[p] >= window_start[friend_curr],
                         start_time[p] + min_duration[friend_curr] <= window_end[friend_curr]
                     ),
                     True
                  ))
    
    # Objective: maximize the number of meetings
    num_meetings = Int('num_meetings')
    s.add(num_meetings == Sum([If(meet[i], 1, 0) for i in range(n_friends)]))
    
    # Maximize the number of meetings
    if s.check() == sat:
        m = s.model()
        num_met = m.evaluate(num_meetings)
        print(f"Maximum number of meetings: {num_met}")
        schedule = []
        for p in range(max_positions):
            friend_idx = m.evaluate(seq[p])
            if friend_idx.as_long() == -1:
                break
            friend_name = names[friend_idx.as_long()]
            st = m.evaluate(start_time[p])
            schedule.append((p, friend_name, st))
        print("Schedule:")
        for pos, name, start in schedule:
            total_minutes = start.as_long()
            hours = total_minutes // 60
            minutes = total_minutes % 60
            print(f"Position {pos}: Meet {name} at {9+hours}:{minutes:02d}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()