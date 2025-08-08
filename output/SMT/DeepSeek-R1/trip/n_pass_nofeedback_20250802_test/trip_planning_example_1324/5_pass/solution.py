from z3 import *

def main():
    total_time = 1324
    activities = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'AA', 'BB', 'CC', 'DD', 'EE', 'FF', 'GG', 'HH', 'II', 'JJ', 'KK', 'LL', 'MM', 'NN', 'OO', 'PP', 'QQ', 'RR', 'SS', 'TT', 'UU', 'VV', 'WW', 'XX', 'YY', 'ZZ', 'AAA', 'BBB', 'CCC', 'DDD', 'EEE', 'FFF', 'GGG', 'HHH', 'III', 'JJJ', 'KKK', 'LLL', 'MMM', 'NNN', 'OOO', 'PPP', 'QQQ', 'RRR', 'SSS', 'TTT', 'UUU', 'VVV', 'WWW', 'XXX', 'YYY', 'ZZZ', 'AAAA', 'BBBB', 'CCCC', 'DDDD', 'EEEE', 'FFFF', 'GGGG', 'HHHH', 'IIII', 'JJJJ', 'KKKK', 'LLLL', 'MMMM', 'NNNN', 'OOOO', 'PPPP', 'QQQQ', 'RRRR', 'SSSS', 'TTTT', 'UUUU', 'VVVV', 'WWWW', 'XXXX', 'YYYY', 'ZZZZ', 'AAAAA', 'BBBBB', 'CCCCC', 'DDDDD', 'EEEEE', 'FFFFF', 'GGGGG', 'HHHHH', 'IIIII', 'JJJJJ', 'KKKKK', 'LLLLL', 'MMMMM', 'NNNNN', 'OOOOO', 'PPPPP', 'QQQQQ', 'RRRRR', 'SSSSS', 'TTTTT', 'UUUUU', 'VVVVV', 'WWWWW', 'XXXXX', 'YYYYY', 'ZZZZZ', 'AAAAAA', 'BBBBBB', 'CCCCCC', 'DDDDDD', 'EEEEEE', 'FFFFFF', 'GGGGGG', 'HHHHHH', 'IIIIII', 'JJJJJJ', 'KKKKKK', 'LLLLLL', 'MMMMMM', 'NNNNNN', 'OOOOOO', 'PPPPPP', 'QQQQQQ', 'RRRRRR', 'SSSSSS', 'TTTTTT', 'UUUUUU', 'VVVVVV', 'WWWWWW', 'XXXXXX', 'YYYYYY', 'ZZZZZZ', 'AAAAAAA', 'BBBBBBB', 'CCCCCCC', 'DDDDDDD', 'EEEEEEE', 'FFFFFFF', 'GGGGGGG', 'HHHHHHH', 'IIIIIII', 'JJJJJJJ', 'KKKKKKK', 'LLLLLLL', 'MMMMMMM', 'NNNNNNN', 'OOOOOOO', 'PPPPPPP', 'QQQQQQQ', 'RRRRRRR', 'SSSSSSS', 'TTTTTTT', 'UUUUUUU', 'VVVVVVV', 'WWWWWWW', 'XXXXXXX', 'YYYYYYY', 'ZZZZZZZ', 'AAAAAAAA', 'BBBBBBBB', 'CCCCCCCC', 'DDDDDDDD', 'EEEEEEEE', 'FFFFFFFF', 'GGGGGGGG', 'HHHHHHHH', 'IIIIIIII', 'JJJJJJJJ', 'KKKKKKKK', 'LLLLLLLL', 'MMMMMMMM', 'NNNNNNNN', 'OOOOOOOO', 'PPPPPPPP', 'QQQQQQQQ', 'RRRRRRRR', 'SSSSSSSS', 'TTTTTTTT', 'UUUUUUUU', 'VVVVVVVV', 'WWWWWWWW', 'XXXXXXXX', 'YYYYYYYY', 'ZZZZZZZZ', 'AAAAAAAAA', 'BBBBBBBBB', 'CCCCCCCCC', 'DDDDDDDDD', 'EEEEEEEEE', 'FFFFFFFFF', 'GGGGGGGGG', 'HHHHHHHHH', 'IIIIIIIII', 'JJJJJJJJJ', 'KKKKKKKKK', 'LLLLLLLLL', 'MMMMMMMMM', 'NNNNNNNNN', 'OOOOOOOOO', 'PPPPPPPPP', 'QQQQQQQQQ', 'RRRRRRRRR', 'SSSSSSSSS', 'TTTTTTTTT', 'UUUUUUUUU', 'VVVVVVVVV', 'WWWWWWWWW', 'XXXXXXXXX', 'YYYYYYYYY', 'ZZZZZZZZZ', 'AAAAAAAAAA', 'BBBBBBBBBB', 'CCCCCCCCCC', 'DDDDDDDDDD', 'EEEEEEEEEE', 'FFFFFFFFFF', 'GGGGGGGGGG', 'HHHHHHHHHH', 'IIIIIIIIII', 'JJJJJJJJJJ', 'KKKKKKKKKK', 'LLLLLLLLLL', 'MMMMMMMMMM', 'NNNNNNNNNN', 'OOOOOOOOOO', 'PPPPPPPPPP', 'QQQQQQQQQQ', 'RRRRRRRRRR', 'SSSSSSSSSS', 'TTTTTTTTTT', 'UUUUUUUUUU', 'VVVVVVVVVV', 'WWWWWWWWWW', 'XXXXXXXXXX', 'YYYYYYYYYY', 'ZZZZZZZZZZ', 'AAAAAAAAAAA', 'BBBBBBBBBBB', 'CCCCCCCCCCC', 'DDDDDDDDDDD', 'EEEEEEEEEEE', 'FFFFFFFFFFF', 'GGGGGGGGGGG', 'HHHHHHHHHHH', 'IIIIIIIIIII', 'JJJJJJJJJJJ', 'KKKKKKKKKKK', 'LLLLLLLLLLL', 'MMMMMMMMMMM', 'NNNNNNNNNNN', 'OOOOOOOOOOO', 'PPPPPPPPPPP', 'QQQQQQQQQQQ', 'RRRRRRRRRRR', 'SSSSSSSSSSS', 'TTTTTTTTTTT', 'UUUUUUUUUUU', 'VVVVVVVVVVV', 'WWWWWWWWWWW', 'XXXXXXXXXXX', 'YYYYYYYYYYY', 'ZZZZZZZZZZZ', 'AAAAAAAAAAAA', 'BBBBBBBBBBBB', 'CCCCCCCCCCCC', 'DDDDDDDDDDDD', 'EEEEEEEEEEEE', 'FFFFFFFFFFF']  # 1324 activities
    durations = [1] * 1324  # All durations are 1
    precedence_constraints = []  # No constraints

    if sum(durations) != total_time:
        print("No solution")
        return

    n = len(activities)
    s = Solver()
    
    # Create Z3 variables for start times
    start_times = [Int(f'start_{i}') for i in range(n)]
    
    # Each start time must be within [0, total_time-1]
    for i in range(n):
        s.add(start_times[i] >= 0)
        s.add(start_times[i] < total_time)
    
    # All start times must be distinct
    s.add(Distinct(start_times))
    
    # Check if satisfiable
    if s.check() == sat:
        m = s.model()
        # Evaluate start times
        eval_starts = [m.evaluate(start_times[i]).as_long() for i in range(n)]
        
        # Output schedule for each activity
        for idx, act in enumerate(activities):
            start_day = eval_starts[idx]
            print(f"{act}: Start at day {start_day}, End at day {start_day}")
        
        # Create activity sequence by sorting by start time
        sorted_activities = sorted(
            [(eval_starts[i], act) for i, act in enumerate(activities)],
            key=lambda x: x[0]
        )
        sequence = [act for (_, act) in sorted_activities]
        print("Order: " + " -> ".join(sequence))
    else:
        print("No solution")

if __name__ == '__main__':
    main()