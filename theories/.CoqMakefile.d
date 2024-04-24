partial.vo partial.glob partial.v.beautified partial.required_vo: partial.v 
partial.vio: partial.v 
partial.vos partial.vok partial.required_vos: partial.v 
commands.vo commands.glob commands.v.beautified commands.required_vo: commands.v partial.vo
commands.vio: commands.v partial.vio
commands.vos commands.vok commands.required_vos: commands.v partial.vos
examples.vo examples.glob examples.v.beautified examples.required_vo: examples.v partial.vo commands.vo
examples.vio: examples.v partial.vio commands.vio
examples.vos examples.vok examples.required_vos: examples.v partial.vos commands.vos
assertions_v2.vo assertions_v2.glob assertions_v2.v.beautified assertions_v2.required_vo: assertions_v2.v examples.vo partial.vo commands.vo
assertions_v2.vio: assertions_v2.v examples.vio partial.vio commands.vio
assertions_v2.vos assertions_v2.vok assertions_v2.required_vos: assertions_v2.v examples.vos partial.vos commands.vos
