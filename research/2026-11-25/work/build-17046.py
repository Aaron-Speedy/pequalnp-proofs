from pathlib import Path
src=Path('lean/PEqualNP/Outside/L_meta_12771.lean').read_text()
s=src[:src.index('def dom_4 :')]+src[src.index('def dom_5 :'):src.index('theorem low_5 :')]
s+='''
theorem low_5 : Lower dom_5 roots_5 goal_5 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff0000ffff0000, 1, 17), (0xffffffff00000000, 1, 33)]
    (by decide +kernel) (by decide +kernel) low_3

'''
s+=src[src.index('def pt6 ('):src.index('def wit : Circuit')]
s+='''def wit : Circuit := ⟨[⟨.or,[1,5]⟩,⟨.and,[0,6]⟩,⟨.and,[2,3]⟩,
  ⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[10,4]⟩,⟨.and,[9,11]⟩,
  ⟨.or,[7,8]⟩,⟨.or,[13,12]⟩],14⟩
'''
s+=src[src.index('theorem wmono :'):]
s=s.replace('4277075694','4277075690').replace('0xfeeefeeefeeefee8',hex(18369900215343709928)).replace('L_meta_12771','L_meta_17045')
Path('.pnp/Positive17045.lean').write_text(s)
