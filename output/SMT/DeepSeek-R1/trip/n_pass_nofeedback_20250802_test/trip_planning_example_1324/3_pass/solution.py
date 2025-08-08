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
    # Create Z3 variables for activity order
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Each position must have a valid activity index
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    
    # All activities must be distinct (permutation constraint)
    s.add(Distinct(order))
    
    # Check if satisfiable
    if s.check() == sat:
        m = s.model()
        activity_schedule = {}
        sequence = []
        
        # Extract schedule from model
        for pos in range(n):
            act_idx = m.evaluate(order[pos]).as_long()
            act_name = activities[act_idx]
            # Start time = position index, end time = position index (duration=1)
            activity_schedule[act_name] = (pos, pos)
            sequence.append(act_name)
        
        # Output schedule for each activity
        for act in activities:
            start_day, end_day = activity_schedule[act]
            print(f"{act}: Start at day {start_day}, End at day {end_day}")
        
        # Output activity sequence
        print("Order: " + " -> ".join(sequence))
    else:
        print("No solution")

if __name__ == '__main__':
    main()