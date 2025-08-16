import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    found = False
    solution = None
    
    for n in itertools.permutations(names):
        if n[2] == 'Peter':
            continue
        
        for s in itertools.permutations(smoothies):
            idx_eric = n.index('Eric')
            if s[idx_eric] != 'dragonfruit':
                continue
            
            idx_desert = s.index('desert')
            idx_watermelon = s.index('watermelon')
            if idx_watermelon <= idx_desert:
                continue
            
            for c in itertools.permutations(cigars):
                if c[0] == 'blue master':
                    continue
                
                idx_dunhill = c.index('dunhill')
                if s[idx_dunhill] != 'cherry':
                    continue
                
                if c[idx_eric] != 'pall mall':
                    continue
                
                for h in itertools.permutations(heights):
                    if h[2] != 'tall':
                        continue
                    
                    idx_very_short = h.index('very short')
                    if idx_dunhill <= idx_very_short:
                        continue
                    
                    if h[idx_dunhill] != 'short':
                        continue
                    
                    for p in itertools.permutations(phones):
                        idx_samsung = p.index('samsung galaxy s21')
                        idx_iphone = p.index('iphone 13')
                        if idx_iphone != idx_samsung + 1:
                            continue
                        
                        if p[idx_very_short] != 'iphone 13':
                            continue
                        
                        idx_prince = c.index('prince')
                        idx_oneplus = p.index('oneplus 9')
                        if idx_prince != idx_oneplus:
                            continue
                        
                        idx_arnold = n.index('Arnold')
                        idx_google = p.index('google pixel 6')
                        if idx_arnold != idx_google:
                            continue
                        
                        found = True
                        solution = (n, s, c, h, p)
                        break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    
    if not found:
        rows = []
    else:
        n_perm, s_perm, c_perm, h_perm, p_perm = solution
        rows = []
        for i in range(4):
            rows.append([str(i+1), n_perm[i], s_perm[i], c_perm[i], h_perm[i], p_perm[i]])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()